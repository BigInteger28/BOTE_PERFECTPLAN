//go:build ignore

// perfectplan.go - zoekt de "perfecte" engines (of vaste zettenreeksen, of een combinatie) tegen een
// lijst tegenstanders.
//
// Starten:   go run perfectplan.go
// Bouwen:    go build -o perfectplan perfectplan.go
// (het bestand heeft de build-tag "ignore" zodat het niet botst met main.go in dezelfde map)
//
// Wat het doet
//   - De gebruiker geeft tegenstander-engines in (zelfde formaat als main.go: 12 tekens diepte-engine,
//     of 13 letters = vaste zettenreeks; "naam:level:code" mag ook, of "@bestand.txt" om een bestand te laden).
//   - De gebruiker geeft op hoeveel zetten (1-13) er gespeeld worden; de partij wordt na die zetten afgebroken en de
//     score na die zetten telt. Minder zetten = veel kleinere zoekruimte = sneller resultaat.
//   - Optioneel geeft de gebruiker beginzetten in (bv. WVAL): alle gevonden engines beginnen daarmee.
//   - Het programma zoekt de N (standaard 3) beste engines. Een engine is een vaste zettenreeks (13 letters),
//     een diepte-engine (12 cijfers) of een combinatie (letters = vaste zetten, daarna dieptecijfers).
//   - Rangschikking: 1) zo weinig mogelijk verloren matches (liefst 0, anders 1, anders 2, ...),
//     2) hoogste score. Per match: winst = 10 + voorsprong, verlies = -10 + (negatief) verschil, gelijk = eigen punten.
//   - Meerdere cores en geheugen worden gebruikt (de gebruiker kan dit instellen). Kleine zoekruimtes worden
//     volledig (exhaustief) doorzocht, grote met een parallelle lokale zoekactie met herstarts.
package main

import (
	"bufio"
	"fmt"
	"math"
	"math/rand"
	"os"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// ---------- simulatie (zelfde regels als main.go) ----------

var elementsDepthArray [256][4]byte
var moveToIndexArray [256]int

func init() {
	elementsDepthArray['W'] = [4]byte{'L', 'A', 'V', 'W'}
	elementsDepthArray['V'] = [4]byte{'W', 'L', 'A', 'V'}
	elementsDepthArray['A'] = [4]byte{'V', 'W', 'L', 'A'}
	elementsDepthArray['L'] = [4]byte{'A', 'V', 'W', 'L'}
	moveToIndexArray['W'] = 0
	moveToIndexArray['V'] = 1
	moveToIndexArray['A'] = 2
	moveToIndexArray['L'] = 3
	moveToIndexArray['D'] = 4
}

var moveWins = [5][5]uint8{
	{0, 1, 0, 2, 0},
	{2, 0, 1, 0, 0},
	{0, 2, 0, 1, 0},
	{1, 0, 2, 0, 0},
	{0, 0, 0, 0, 0},
}

var depthToElement = [5]byte{'W', 'V', 'A', 'L', 'D'}
var letters = [5]byte{'W', 'V', 'A', 'L', 'D'}
var letterLimits = [5]int{3, 3, 3, 3, 1}

func getElementFromCode(depth int) byte {
	if depth < 1 || depth > 5 {
		return 0
	}
	return depthToElement[depth-1]
}

func getElementByDepth(prev byte, depth int) byte {
	if depth == 5 {
		return 'D'
	}
	if prev == 0 {
		return 0
	}
	if prev == 'D' {
		prev = 'L'
	}
	return elementsDepthArray[prev][depth-1]
}

func chooseAvailableElement(target byte, available *[5]int) byte {
	if available[moveToIndexArray[target]] > 0 {
		return target
	}
	current := target
	for i := 0; i < 5; i++ {
		current = elementsDepthArray[current][0]
		if available[moveToIndexArray[current]] > 0 {
			return current
		}
	}
	if available[4] > 0 {
		return 'D'
	}
	return 0
}

func getLastElement(available *[5]int) byte {
	for i, c := range depthToElement {
		if available[i] > 0 {
			return c
		}
	}
	return 0
}

func determineWinner(m1, m2 byte) int {
	return int(moveWins[moveToIndexArray[m1]][moveToIndexArray[m2]])
}

func isMoveLetter(c byte) bool {
	return c == 'W' || c == 'V' || c == 'A' || c == 'L' || c == 'D'
}

func resolveTarget(ch byte, i int, oppMoves []byte) byte {
	if isMoveLetter(ch) {
		return ch
	}
	digit := int(ch - '0')
	if digit >= 6 {
		base := digit - 5
		if i < 2 {
			return getElementFromCode(base)
		}
		return getElementByDepth(oppMoves[i-2], base)
	}
	if i == 0 {
		return getElementFromCode(digit)
	}
	return getElementByDepth(oppMoves[i-1], digit)
}

// strat is een speler: een diepte-engine/combinatie (12 tekens) of een vaste zettenreeks (13 letters).
type strat struct {
	code  [13]byte
	fixed bool
}

func newStrat(e string) strat {
	var s strat
	copy(s.code[:], e)
	s.fixed = len(e) == 13
	return s
}

// play speelt twee strategieën tegen elkaar en geeft het aantal gewonnen rondes (van 13) per speler.
func play(a, b *strat, rounds int) (sa, sb int) {
	av := [5]int{3, 3, 3, 3, 1}
	bv := [5]int{3, 3, 3, 3, 1}
	var am, bm [13]byte
	dl := rounds
	if dl > 12 {
		dl = 12
	}
	for i := 0; i < dl; i++ {
		var ma, mb byte
		if a.fixed {
			ma = a.code[i]
		} else {
			ma = chooseAvailableElement(resolveTarget(a.code[i], i, bm[:]), &av)
			if ma == 0 {
				ma = getLastElement(&av)
			}
			if ma != 0 {
				av[moveToIndexArray[ma]]--
			}
		}
		if b.fixed {
			mb = b.code[i]
		} else {
			mb = chooseAvailableElement(resolveTarget(b.code[i], i, am[:]), &bv)
			if mb == 0 {
				mb = getLastElement(&bv)
			}
			if mb != 0 {
				bv[moveToIndexArray[mb]]--
			}
		}
		am[i], bm[i] = ma, mb
	}
	if rounds == 13 {
		if a.fixed {
			am[12] = a.code[12]
		} else if am[12] = getLastElement(&av); am[12] == 0 {
			am[12] = 'W'
		}
		if b.fixed {
			bm[12] = b.code[12]
		} else if bm[12] = getLastElement(&bv); bm[12] == 0 {
			bm[12] = 'W'
		}
	}
	for i := 0; i < rounds; i++ {
		switch determineWinner(am[i], bm[i]) {
		case 1:
			sa++
		case 2:
			sb++
		}
	}
	return
}

// ---------- evaluatie ----------

type res struct {
	losses, wins, draws int
	score               int
	fails               int // aantal must-win engines waar NIET van gewonnen wordt (moet 0 zijn)
}

// mustFrom: opps[mustFrom:] zijn must-win engines (er moet altijd van gewonnen worden). Wordt per run ingesteld.
// Must-win engines tellen niet mee in verliezen/winst/score, alleen in fails.
var mustFrom = 1 << 30

// val: 1) alle must-win engines verslaan, 2) wint van alle tegenstanders (geen verlies, geen gelijkspel),
// 3) minder verliezen (een gelijkspel mag, het is geen verlies), 4) hogere score.
func (r res) val() int64 {
	v := -int64(r.fails)*100_000_000_000 - int64(r.losses)*10_000_000 + int64(r.score)
	if r.losses == 0 && r.draws == 0 {
		v += 1_000_000_000 // wint van alle tegenstanders: altijd beter dan engines met gelijkspelen
	}
	return v
}

func evaluate(c *strat, opps []strat, rounds int) res {
	var r res
	for i := range opps {
		s1, s2 := play(c, &opps[i], rounds)
		if i >= mustFrom {
			if s1 <= s2 {
				r.fails++
			}
			continue
		}
		switch {
		case s1 > s2:
			r.wins++
			r.score += s1 - s2 + 10
		case s1 < s2:
			r.losses++
			r.score += s1 - s2 - 10
		default:
			r.draws++
			r.score += s1
		}
	}
	return r
}

// ---------- kandidaten ----------

type cand struct {
	b     [13]byte
	n     int  // aantal gespeelde zetten van deze kandidaat (diepte: max 12)
	fixed bool // vaste zettenreeks (alleen letters)
}

func (c cand) String() string { return string(c.b[:c.n]) }
func (c cand) strat() strat   { return strat{code: c.b, fixed: c.fixed} }

func symIdx(c byte) uint64 {
	if c >= '1' && c <= '9' {
		return uint64(c-'1') + 1
	}
	switch c {
	case 'W':
		return 10
	case 'V':
		return 11
	case 'A':
		return 12
	case 'L':
		return 13
	case 'D':
		return 14
	}
	return 0
}

func (c cand) key() uint64 {
	var k uint64
	for i := 0; i < c.n; i++ {
		k = k<<4 | symIdx(c.b[i])
	}
	if c.fixed {
		k |= 1 << 60
	}
	return k
}

func hamming(a, b cand) int {
	d := 0
	for i := 0; i < 13; i++ {
		if a.b[i] != b.b[i] {
			d++
		}
	}
	return d
}

// valid controleert of een kandidaat binnen de regels valt.
// 13 tekens: precies de vaste zetten (3xW 3xV 3xA 3xL 1xD). 12 tekens: eerst maximaal maxLetters letters
// (vaste zetten), dan cijfers 1-9; de D-zet is gelijk aan cijfer 5 (samen maximaal één keer).
// depthMax: hoogste dieptecijfer dat in de gezochte engines mag voorkomen ('9' = uitgebreid 1-9, '5' = 1-5).
var depthMax byte = '9'

// exactLetters: gewenst aantal vaste letters (beginzetten meegeteld) of -1 = onbeperkt. Wordt per run ingesteld.
var exactLetters = -1

func valid(c *cand, maxLetters int) bool {
	if c.fixed {
		if exactLetters >= 0 && exactLetters != c.n {
			return false
		}
		var cnt [5]int
		for i := 0; i < c.n; i++ {
			if !isMoveLetter(c.b[i]) {
				return false
			}
			idx := moveToIndexArray[c.b[i]]
			cnt[idx]++
			if cnt[idx] > letterLimits[idx] {
				return false
			}
		}
		return true
	}
	k := 0
	for k < c.n && isMoveLetter(c.b[k]) {
		k++
	}
	if k > maxLetters || (exactLetters >= 0 && k != exactLetters) {
		return false
	}
	var cnt [5]int
	for i := 0; i < k; i++ {
		idx := moveToIndexArray[c.b[i]]
		cnt[idx]++
		if cnt[idx] > letterLimits[idx] {
			return false
		}
	}
	fives := cnt[4]
	for i := k; i < c.n; i++ {
		ch := c.b[i]
		if ch < '1' || ch > depthMax || (i == 0 && ch > '5') {
			return false
		}
		if ch == '5' {
			fives++
		}
	}
	return fives <= 1
}

// ---------- gedeelde zoekstructuur ----------

// Letters (vaste zetten) mogen onbeperkt: elke engine begint met 0..M letters (met de limiet 3xW/V/A/L en 1xD)
// en gaat daarna verder met dieptecijfers. Alles van 'allemaal letters' tot 'allemaal cijfers' wordt bekeken.

type pool struct {
	mu      sync.Mutex
	items   []item
	max     int
	minDist int
	floor   atomic.Int64 // waarde van de slechtste engine als de pool vol is, anders MinInt64
	changed atomic.Int64 // tijdstip (UnixNano) van de laatste wijziging
}

type item struct {
	c   cand
	r   res
	val int64
}

func newPool(max, minDist int) *pool {
	p := &pool{max: max, minDist: minDist}
	p.floor.Store(math.MinInt64)
	p.changed.Store(time.Now().UnixNano())
	return p
}

func (p *pool) refresh() {
	p.changed.Store(time.Now().UnixNano())
	if len(p.items) < p.max {
		p.floor.Store(math.MinInt64)
		return
	}
	w := p.items[0].val
	for _, it := range p.items {
		if it.val < w {
			w = it.val
		}
	}
	p.floor.Store(w)
}

// offer zet een kandidaat in de pool als hij goed genoeg en voldoende verschillend is van de andere engines.
func (p *pool) offer(it item) bool {
	if it.val <= p.floor.Load() {
		return false
	}
	p.mu.Lock()
	defer p.mu.Unlock()
	var near []int
	for i, o := range p.items {
		if o.c == it.c {
			return false
		}
		if hamming(o.c, it.c) < p.minDist {
			if it.val <= o.val {
				return false // een even goede of betere buur bestaat al
			}
			near = append(near, i)
		}
	}
	if len(near) > 0 {
		sort.Sort(sort.Reverse(sort.IntSlice(near)))
		for _, i := range near {
			p.items[i] = p.items[len(p.items)-1]
			p.items = p.items[:len(p.items)-1]
		}
		p.items = append(p.items, it)
		p.refresh()
		return true
	}
	if len(p.items) < p.max {
		p.items = append(p.items, it)
		p.refresh()
		return true
	}
	w := 0
	for i := range p.items {
		if p.items[i].val < p.items[w].val {
			w = i
		}
	}
	if it.val > p.items[w].val {
		p.items[w] = it
		p.refresh()
		return true
	}
	return false
}

func (p *pool) snapshot() []item {
	p.mu.Lock()
	defer p.mu.Unlock()
	out := append([]item(nil), p.items...)
	sort.Slice(out, func(i, j int) bool { return out[i].val > out[j].val })
	return out
}

// seenSet onthoudt welke kandidaten al geëvalueerd zijn (gebruikt het opgegeven geheugen).
type seenSet struct {
	shards [64]struct {
		mu sync.Mutex
		m  map[uint64]struct{}
	}
	perShard int
}

func newSeenSet(maxEntries int) *seenSet {
	s := &seenSet{perShard: maxEntries/64 + 1}
	for i := range s.shards {
		s.shards[i].m = make(map[uint64]struct{})
	}
	return s
}

// add geeft true als de sleutel nieuw is.
func (s *seenSet) add(k uint64) bool {
	sh := &s.shards[(k*0x9E3779B97F4A7C15)>>58]
	sh.mu.Lock()
	defer sh.mu.Unlock()
	if _, ok := sh.m[k]; ok {
		return false
	}
	if len(sh.m) < s.perShard {
		sh.m[k] = struct{}{}
	}
	return true
}

type searcher struct {
	opps       []strat
	prefix     string
	P          int  // lengte van de beginzetten
	hasDigit   bool // de beginzetten bevatten al cijfers: er komen geen letters meer bij
	M          int  // aantal te spelen zetten
	dl         int  // lengte van een diepte-engine = min(M, 12)
	maxLetters int
	p          *pool
	seen       *seenSet
	evaluated  atomic.Int64
	stop       atomic.Bool
	exhaustive atomic.Int64 // aantal exhaustief doorlopen kandidaten
}

func (s *searcher) tryCand(c cand) (item, bool) {
	var st = c.strat()
	r := evaluate(&st, s.opps, s.M)
	s.evaluated.Add(1)
	return item{c: c, r: r, val: r.val()}, true
}

func (s *searcher) randDigit(rng *rand.Rand, pos int) byte {
	if pos == 0 {
		return byte('1' + rng.Intn(5))
	}
	return byte('1' + rng.Intn(int(depthMax-'0')))
}

func (s *searcher) randomCand(rng *rand.Rand) cand {
	for try := 0; try < 1000; try++ {
		var c cand
		copy(c.b[:], s.prefix)
		fixedOK := false // een engine heeft maximaal 12 zetten: een vaste reeks van M letters is gelijk aan een engine met M letters
		depthOK := exactLetters < 0 || exactLetters <= s.dl
		if fixedOK && (!depthOK || rng.Intn(100) < 10) { // vaste zettenreeks
			c.n = s.M
			c.fixed = true
			var cnt [5]int
			for i := 0; i < s.P; i++ {
				cnt[moveToIndexArray[c.b[i]]]++
			}
			var rest []byte
			for i, ch := range letters {
				for j := cnt[i]; j < letterLimits[i]; j++ {
					rest = append(rest, ch)
				}
			}
			rng.Shuffle(len(rest), func(i, j int) { rest[i], rest[j] = rest[j], rest[i] })
			copy(c.b[s.P:s.M], rest)
		} else {
			c.n = s.dl
			extra := rng.Intn(4)
			if rng.Intn(100) < 60 {
				extra = rng.Intn(s.dl - s.P + 1) // alles van geen tot allemaal letters
			}
			if exactLetters >= 0 {
				extra = exactLetters - s.P
			}
			if s.hasDigit {
				extra = 0
			}
			pos := s.P
			for ; pos < c.n && pos < s.P+extra; pos++ {
				c.b[pos] = letters[rng.Intn(5)]
			}
			for ; pos < c.n; pos++ {
				c.b[pos] = s.randDigit(rng, pos)
			}
		}
		if valid(&c, s.maxLetters) {
			return c
		}
	}
	var c cand
	copy(c.b[:], s.prefix)
	c.n = s.dl
	return c
}

func (s *searcher) mutate(c cand, rng *rand.Rand) cand {
	free := c.n - s.P
	if free <= 0 {
		return c
	}
	changes := 1
	if rng.Intn(3) == 0 {
		changes++
	}
	if rng.Intn(10) == 0 {
		changes++
	}
	for n := 0; n < changes; n++ {
		for try := 0; try < 30; try++ {
			d := c
			if c.fixed {
				if rng.Intn(3) == 0 {
					d.b[s.P+rng.Intn(free)] = letters[rng.Intn(5)]
				} else if free >= 2 {
					i, j := s.P+rng.Intn(free), s.P+rng.Intn(free)
					d.b[i], d.b[j] = d.b[j], d.b[i]
				}
			} else {
				k := 0
				for k < c.n && isMoveLetter(d.b[k]) {
					k++
				}
				switch r := rng.Intn(100); {
				case r < 12 && exactLetters < 0: // het letter-voorvoegsel langer of korter maken
					if rng.Intn(2) == 0 && k < c.n && k >= s.P {
						d.b[k] = letters[rng.Intn(5)]
					} else if k > s.P {
						d.b[k-1] = s.randDigit(rng, k-1)
					}
				case r < 30 && free >= 2:
					i, j := s.P+rng.Intn(free), s.P+rng.Intn(free)
					d.b[i], d.b[j] = d.b[j], d.b[i]
				default:
					pos := s.P + rng.Intn(free)
					if pos < k {
						d.b[pos] = letters[rng.Intn(5)]
					} else {
						d.b[pos] = s.randDigit(rng, pos)
					}
				}
			}
			if d != c && valid(&d, s.maxLetters) {
				c = d
				break
			}
		}
	}
	return c
}

// exhaustive doorloopt alle engines "beginzetten + alleen cijfers". Werkers halen om beurt brokken op.
// ---------- volledige doorloop (DFS) ----------
//
// De boom: een engine begint met k >= P letters (vaste zetten) en gaat daarna verder met cijfers.
// Via DFS wordt elke ronde maar één keer per tegenstander gespeeld voor alle engines met hetzelfde begin,
// dat is ongeveer M keer sneller dan elke engine apart simuleren.

type node struct {
	pos       int
	inLetters bool
	cnt       [4]int8 // aantal W V A L
	used5     bool    // D-letter of cijfer 5 al gebruikt
}

func (s *searcher) children(n node, out []byte) []byte {
	out = out[:0]
	if n.pos < s.P {
		return append(out, s.prefix[n.pos])
	}
	if n.inLetters && n.pos < s.dl && (exactLetters < 0 || n.pos < exactLetters) {
		for i, ch := range letters {
			if i < 4 && int(n.cnt[i]) >= letterLimits[i] {
				continue
			}
			if i == 4 && n.used5 {
				continue
			}
			out = append(out, ch)
		}
	}
	maxD := depthMax
	if n.pos == 0 {
		maxD = '5'
	}
	if exactLetters >= 0 && n.pos < exactLetters {
		return out // hier moet nog een letter komen
	}
	for d := byte('1'); d <= maxD; d++ {
		if d == '5' && n.used5 {
			continue
		}
		out = append(out, d)
	}
	return out
}

func (n node) next(ch byte) node {
	n.pos++
	if isMoveLetter(ch) {
		if ch == 'D' {
			n.used5 = true
		} else {
			n.cnt[moveToIndexArray[ch]]++
		}
		return n
	}
	n.inLetters = false
	if ch == '5' {
		n.used5 = true
	}
	return n
}

// countLeaves telt het aantal engines in de boom (met geheugen).
func (s *searcher) countLeaves() float64 {
	memo := map[node]float64{}
	var rec func(n node) float64
	rec = func(n node) float64 {
		if n.pos == s.dl {
			return 1
		}
		if v, ok := memo[n]; ok {
			return v
		}
		t := 0.0
		for _, ch := range s.children(n, nil) {
			t += rec(n.next(ch))
		}
		memo[n] = t
		return t
	}
	return rec(node{inLetters: true})
}

type ost struct {
	av, bv [5]int
	am, bm [13]byte
	sa, sb int
}

func stepOpp(i int, ch byte, src, dst *ost, o *strat) {
	*dst = *src
	ma := chooseAvailableElement(resolveTarget(ch, i, src.bm[:]), &dst.av)
	if ma == 0 {
		ma = getLastElement(&dst.av)
	}
	if ma != 0 {
		dst.av[moveToIndexArray[ma]]--
	}
	var mb byte
	if o.fixed {
		mb = o.code[i]
	} else {
		mb = chooseAvailableElement(resolveTarget(o.code[i], i, src.am[:]), &dst.bv)
		if mb == 0 {
			mb = getLastElement(&dst.bv)
		}
		if mb != 0 {
			dst.bv[moveToIndexArray[mb]]--
		}
	}
	dst.am[i], dst.bm[i] = ma, mb
	switch determineWinner(ma, mb) {
	case 1:
		dst.sa++
	case 2:
		dst.sb++
	}
}

type dfsWorker struct {
	s      *searcher
	levels [][]ost
	buf    [13]byte
	count  int64
	limit  int64 // 0 = onbeperkt; anders stoppen na zoveel bladeren (voor de snelheidsmeting)
}

// evalLeaf berekent het totaalresultaat uit de toestanden na alle gespeelde ronden; last = 13e (automatische) zet erbij.
func evalLeaf(cur []ost, opps []strat, last bool) res {
	var r res
	for j := range cur {
		o := &cur[j]
		sa, sb := o.sa, o.sb
		if last {
			ma := getLastElement(&o.av)
			if ma == 0 {
				ma = 'W'
			}
			var mb byte
			if opps[j].fixed {
				mb = opps[j].code[12]
			} else if mb = getLastElement(&o.bv); mb == 0 {
				mb = 'W'
			}
			switch determineWinner(ma, mb) {
			case 1:
				sa++
			case 2:
				sb++
			}
		}
		if j >= mustFrom {
			if sa <= sb {
				r.fails++
			}
			continue
		}
		switch {
		case sa > sb:
			r.wins++
			r.score += sa - sb + 10
		case sa < sb:
			r.losses++
			r.score += sa - sb - 10
		default:
			r.draws++
			r.score += sa
		}
	}
	return r
}

func (w *dfsWorker) leaf(cur []ost) {
	s := w.s
	r := evalLeaf(cur, s.opps, s.M == 13)
	w.count++
	if w.count&1023 == 0 {
		s.evaluated.Add(1024)
	}
	if v := r.val(); v > s.p.floor.Load() {
		c := cand{b: w.buf, n: s.dl}
		s.p.offer(item{c: c, r: r, val: v})
	}
}

func (w *dfsWorker) rec(n node, cur []ost) bool {
	s := w.s
	if n.pos == s.dl {
		w.leaf(cur)
		return w.limit == 0 || w.count < w.limit
	}
	if n.pos < s.dl-1 && s.stop.Load() {
		return false
	}
	var chBuf [16]byte
	chs := s.children(n, chBuf[:0])
	nxt := w.levels[n.pos+1]
	for _, ch := range chs {
		for j := range cur {
			stepOpp(n.pos, ch, &cur[j], &nxt[j], &s.opps[j])
		}
		w.buf[n.pos] = ch
		if !w.rec(n.next(ch), nxt) {
			return false
		}
	}
	return true
}

func newDFSWorker(s *searcher) *dfsWorker {
	w := &dfsWorker{s: s, levels: make([][]ost, s.dl+1)}
	for i := range w.levels {
		w.levels[i] = make([]ost, len(s.opps))
	}
	return w
}

// runTask speelt het begin van de taak en doorloopt de rest van de boom. Geeft true als alles doorlopen is.
func (w *dfsWorker) runTask(task []byte) bool {
	s := w.s
	for j := range w.levels[0] {
		w.levels[0][j] = ost{av: [5]int{3, 3, 3, 3, 1}, bv: [5]int{3, 3, 3, 3, 1}}
	}
	n := node{inLetters: true}
	for pos, ch := range task {
		for j := range w.levels[pos] {
			stepOpp(pos, ch, &w.levels[pos][j], &w.levels[pos+1][j], &s.opps[j])
		}
		w.buf[pos] = ch
		n = n.next(ch)
	}
	return w.rec(n, w.levels[n.pos])
}

// measureLeafNs meet hoeveel ns één engine (blad) kost, op een paar verspreide taken.
func (s *searcher) measureLeafNs(tasks [][]byte) float64 {
	w := newDFSWorker(s)
	w.limit = 3000
	var leaves int64
	t0 := time.Now()
	for i := 0; i < 5; i++ {
		w.count = 0
		w.runTask(tasks[i*len(tasks)/5])
		leaves += w.count
	}
	if leaves == 0 {
		return 1
	}
	return float64(time.Since(t0).Nanoseconds()) / float64(leaves)
}

// exhaustiveWorker haalt taken (begin van een engine) op en doorloopt de rest van de boom.
func (s *searcher) exhaustiveWorker(tasks [][]byte, next *atomic.Int64, doneTasks *atomic.Int64) {
	w := newDFSWorker(s)
	for !s.stop.Load() {
		ti := int(next.Add(1) - 1)
		if ti >= len(tasks) {
			return
		}
		if w.runTask(tasks[ti]) {
			doneTasks.Add(1)
		}
		s.evaluated.Add(w.count & 1023)
		w.count = 0
	}
}

// makeTasks geeft alle geldige beginnen van lengte min(dl, P+3).
func (s *searcher) makeTasks() [][]byte {
	cutLen := s.P + 3
	if cutLen > s.dl {
		cutLen = s.dl
	}
	var tasks [][]byte
	var rec func(n node, cur []byte)
	rec = func(n node, cur []byte) {
		if n.pos == cutLen {
			tasks = append(tasks, append([]byte(nil), cur...))
			return
		}
		for _, ch := range s.children(n, nil) {
			rec(n.next(ch), append(cur, ch))
		}
	}
	rec(node{inLetters: true}, nil)
	return tasks
}

// localSearch: parallelle hill-climbing met plateau-zetten, kleine kans op achteruitgang en herstarts.
func (s *searcher) localSearch(rng *rand.Rand) {
	var cur cand
	var curVal int64
	stall := 0
	restart := func() {
		for try := 0; try < 50; try++ {
			if rng.Intn(100) < 35 {
				snap := s.p.snapshot()
				if len(snap) > 0 {
					cur = snap[rng.Intn(len(snap))].c
					for i := 0; i < 3+rng.Intn(3); i++ {
						cur = s.mutate(cur, rng)
					}
				} else {
					cur = s.randomCand(rng)
				}
			} else {
				cur = s.randomCand(rng)
			}
			if s.seen.add(cur.key()) {
				break
			}
		}
		it, _ := s.tryCand(cur)
		curVal = it.val
		s.p.offer(it)
		stall = 0
	}
	restart()
	for !s.stop.Load() {
		cand := s.mutate(cur, rng)
		stall++
		if cand == cur || !s.seen.add(cand.key()) {
			if stall > 600 {
				restart()
			}
			continue
		}
		it, _ := s.tryCand(cand)
		s.p.offer(it)
		switch {
		case it.val > curVal:
			cur, curVal = cand, it.val
			stall = 0
		case it.val == curVal:
			cur = cand
		case it.val > curVal-30 && rng.Intn(100) < 3:
			cur, curVal = cand, it.val
		}
		if stall > 600 {
			restart()
		}
	}
}

// ---------- invoer / uitvoer ----------

func parseEngineCode(input string) string {
	parts := strings.Split(input, ":")
	engine := strings.TrimSpace(input)
	if len(parts) > 2 {
		engine = strings.TrimSpace(parts[2])
	}
	return strings.ToUpper(engine)
}

func isValidDepthCode(engine string) bool {
	if len(engine) != 12 {
		return false
	}
	seenDigit := false
	for i := 0; i < len(engine); i++ {
		c := engine[i]
		switch {
		case c >= '1' && c <= '9':
			seenDigit = true
		case isMoveLetter(c):
			if seenDigit {
				return false
			}
		default:
			return false
		}
	}
	return true
}

func isFixed13(e string) bool { return len(e) == 13 && strings.Trim(e, "WVALD") == "" }

func addOpponent(line string, out *[]string, names *[]string) {
	line = strings.TrimSpace(line)
	if line == "" {
		return
	}
	e := parseEngineCode(line)
	if isValidDepthCode(e) || isFixed13(e) {
		*out = append(*out, e)
		name := e
		if p := strings.Split(line, ":"); len(p) > 2 {
			name = strings.TrimSpace(p[0])
		}
		*names = append(*names, name)
	} else {
		fmt.Printf("Ongeldige engine code '%s' overgeslagen.\n", e)
	}
}

// readEngines leest engines tot '.' of een lege regel. '@bestand' laadt een bestand met engines.
func readEngines(sc *bufio.Scanner) (engines, names []string) {
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "." || line == "" {
			break
		}
		if strings.HasPrefix(line, "@") {
			data, err := os.ReadFile(strings.TrimSpace(line[1:]))
			if err != nil {
				fmt.Println("Kan bestand niet lezen:", err)
				continue
			}
			for _, l := range strings.Split(string(data), "\n") {
				addOpponent(l, &engines, &names)
			}
			continue
		}
		addOpponent(line, &engines, &names)
	}
	return
}

func askInt(sc *bufio.Scanner, prompt string, def, min, max int) int {
	fmt.Printf("%s (default %d): ", prompt, def)
	if !sc.Scan() {
		return def
	}
	txt := strings.TrimSpace(sc.Text())
	if txt == "" {
		return def
	}
	n, err := strconv.Atoi(txt)
	if err != nil || n < min || n > max {
		fmt.Printf("Ongeldige invoer, default %d gebruikt.\n", def)
		return def
	}
	return n
}

// askPrefix vraagt de beginzetten: eerst letters (W/V/A/L/D = vaste zetten), daarna eventueel cijfers (dieptes), bv. AWA11.
// Leeg = geen.
func askPrefix(sc *bufio.Scanner, moves int) string {
	for {
		fmt.Printf("Beginzetten? (letters W/V/A/L/D, daarna eventueel cijfers 1-%c, bv. WVAL of AWA11, leeg = geen): ", depthMax)
		if !sc.Scan() {
			return ""
		}
		txt := strings.ToUpper(strings.NewReplacer(" ", "", ",", "", "-", "").Replace(sc.Text()))
		if msg := checkPrefix(txt, moves); msg != "" {
			fmt.Println("Ongeldig:", msg)
			continue
		}
		return txt
	}
}

// checkPrefix geeft een foutmelding, of "" als de beginzetten geldig zijn.
func checkPrefix(txt string, moves int) string {
	if len(txt) > moves {
		return fmt.Sprintf("maximaal %d tekens.", moves)
	}
	var cnt [5]int
	fives := 0
	seenDigit := false
	for i := 0; i < len(txt); i++ {
		c := txt[i]
		switch {
		case isMoveLetter(c):
			if seenDigit {
				return "letters moeten vóór de cijfers staan."
			}
			idx := moveToIndexArray[c]
			cnt[idx]++
			if cnt[idx] > letterLimits[idx] {
				return "max 3x elke letter en 1x D."
			}
			if c == 'D' {
				fives++
			}
		case c >= '1' && c <= depthMax:
			seenDigit = true
			if i == 0 && c > '5' {
				return "de eerste zet als cijfer kan alleen 1-5 zijn."
			}
			if c == '5' {
				fives++
			}
		default:
			return fmt.Sprintf("alleen W V A L D en cijfers 1-%c.", depthMax)
		}
	}
	if fives > 1 {
		return "D en cijfer 5 zijn dezelfde zet en kunnen samen maar 1x voorkomen."
	}
	return ""
}

// askLetterCount vraagt hoeveel vaste elementen (letters) de engines precies hebben, beginzetten meegeteld.
// Leeg = onbeperkt (alles van allemaal letters tot allemaal cijfers wordt bekeken). Geeft -1 bij onbeperkt.
func askLetterCount(sc *bufio.Scanner, prefixLen, moves int) int {
	fmt.Printf("Aantal vaste elementen (letters) in totaal, beginzetten meegeteld (%d-%d, leeg = onbeperkt): ", prefixLen, moves)
	if !sc.Scan() {
		return -1
	}
	txt := strings.TrimSpace(sc.Text())
	if txt == "" {
		return -1
	}
	n, err := strconv.Atoi(txt)
	if err != nil || n < prefixLen || n > moves {
		fmt.Println("Ongeldige invoer, onbeperkt gebruikt.")
		return -1
	}
	return n
}

// askFill vraagt of de engine na de gekozen zetten wordt opgevuld tot 12 zetten met makkelijke dieptes.
func askFill(sc *bufio.Scanner) bool {
	fmt.Printf("Opvullen tot 12 zetten met makkelijke dieptes (max %d reeksen, bv. 11123 of 112211)? (j/n, default n): ", maxFillRuns)
	if !sc.Scan() {
		return false
	}
	t := strings.ToLower(strings.TrimSpace(sc.Text()))
	return t == "j" || t == "ja" || t == "y"
}

func availableMemMB() int {
	data, err := os.ReadFile("/proc/meminfo")
	if err == nil {
		for _, l := range strings.Split(string(data), "\n") {
			if strings.HasPrefix(l, "MemAvailable:") {
				f := strings.Fields(l)
				if len(f) >= 2 {
					if kb, err := strconv.Atoi(f[1]); err == nil {
						return kb / 1024
					}
				}
			}
		}
	}
	return 4096
}

// losersOf geeft de gewone tegenstanders waarvan verloren wordt, en de must-win engines waarvan niet gewonnen wordt.
func losersOf(c cand, opps []strat, rounds int) (lose, notWon []int) {
	st := c.strat()
	for i := range opps {
		s1, s2 := play(&st, &opps[i], rounds)
		if i >= mustFrom {
			if s1 <= s2 {
				notWon = append(notWon, i)
			}
		} else if s1 < s2 {
			lose = append(lose, i)
		}
	}
	return
}

func run(opps []strat, names []string, mustCount int, prefix string, moves, letterCount int, fill bool, size, threads, memMB, seconds int) {
	exactLetters = letterCount
	mustFrom = len(opps) - mustCount
	P := len(prefix)
	dl := moves
	if dl > 12 {
		dl = 12
	}
	minDist := 3
	if f := moves - P; minDist > f {
		minDist = f
	}
	if minDist < 1 {
		minDist = 1
	}
	rounds := moves // bij 12 zetten telt ook de 13e (automatische) zet mee in de score
	if moves == 12 {
		rounds = 13
	}
	s := &searcher{hasDigit: strings.Trim(prefix, "WVALD") != "", opps: opps, prefix: prefix, P: P, M: rounds, dl: dl, p: newPool(size, minDist)}
	s.maxLetters = dl
	s.seen = newSeenSet(memMB * 1_000_000 / 2 / 40)

	// alle zetten liggen vast door de beginzetten: niets te zoeken
	if P >= moves {
		var c cand
		copy(c.b[:], prefix)
		c.n = dl
		it, _ := s.tryCand(c)
		s.p.offer(it)
		report(s, names, fill, threads, seconds)
		return
	}

	leaves := s.countLeaves()
	// snelheid van de volledige doorloop meten op een paar taken (alle cores samen belasten ~30% trager)
	var tasks [][]byte
	if exactLetters <= dl {
		tasks = s.makeTasks()
	}
	if len(tasks) == 0 && exactLetters >= 0 && exactLetters <= dl {
		fmt.Printf("Geen geldige engine met %d vaste letters (let op: max 3x W/V/A/L en 1x D, beginzetten tellen mee).\n", exactLetters)
		return
	}
	nsLeaf, estSec := 0.0, math.Inf(1)
	if len(tasks) > 0 {
		nsLeaf = s.measureLeafNs(tasks)
		estSec = leaves * nsLeaf * 1.3 / float64(threads) / 1e9
	}
	doExhaustive := len(tasks) > 0 && estSec <= 0.95*float64(seconds)
	if doExhaustive {
		fmt.Printf("Zoekruimte %.3g engines (alle letter/cijfer-mixen), geschat %.0fs: wordt volledig doorzocht.\n", leaves, estSec)
	} else {
		if math.IsInf(estSec, 1) {
			fmt.Println("Alleen vaste zettenreeksen mogelijk met dit aantal letters: lokale zoekactie.")
		} else {
			fmt.Printf("Zoekruimte %.3g engines, volledig doorzoeken zou ~%.0fs duren (limiet %ds): lokale zoekactie.\n", leaves, estSec, seconds)
		}
	}
	var nextTask, doneTasks atomic.Int64

	start := time.Now()
	deadline := start.Add(time.Duration(seconds) * time.Second)
	var wg sync.WaitGroup
	for t := 0; t < threads; t++ {
		wg.Add(1)
		go func(seed int64) {
			defer wg.Done()
			rng := rand.New(rand.NewSource(seed))
			if doExhaustive {
				s.exhaustiveWorker(tasks, &nextTask, &doneTasks)
			}
			if s.stop.Load() {
				return
			}
			s.localSearch(rng)
		}(time.Now().UnixNano() + int64(t)*104729)
	}

	stall := time.Duration(seconds) * time.Second / 4
	if stall < 5*time.Second {
		stall = 5 * time.Second
	}
	ticker := time.NewTicker(300 * time.Millisecond)
	for range ticker.C {
		snap := s.p.snapshot()
		perfect, best := 0, int64(0)
		for _, it := range snap {
			if it.r.losses == 0 && it.r.fails == 0 {
				perfect++
			}
		}
		if len(snap) > 0 {
			best = int64(snap[0].r.score)
		}
		el := time.Since(start)
		fmt.Printf("\r[%4.1fs] pool %d/%d, %d zonder verlies, beste score %d, %s getest (%s/s)   ",
			el.Seconds(), len(snap), size, perfect, best, human(float64(s.evaluated.Load())), human(float64(s.evaluated.Load())/el.Seconds()))
		idle := time.Since(time.Unix(0, s.p.changed.Load()))
		if time.Now().After(deadline) {
			break
		}
		// volledig doorzocht: bij M<13 is het resultaat bewezen optimaal
		if doExhaustive && int(doneTasks.Load()) == len(tasks) && true {
			break
		}
		// alles al gewonnen/gelijk en de pool staat vol: stoppen als er niets meer verbetert
		if len(snap) == size && perfect == size && idle > stall && el > stall {
			break
		}
	}
	ticker.Stop()
	s.stop.Store(true)
	wg.Wait()
	fmt.Printf("\r%s kandidaten getest in %.1fs%60s\n", human(float64(s.evaluated.Load())), time.Since(start).Seconds(), "")
	report(s, names, fill, threads, seconds)
}

func report(s *searcher, names []string, fill bool, threads, seconds int) {
	snap := s.p.snapshot()
	if len(snap) == 0 {
		fmt.Println("Geen engines gevonden.")
		return
	}
	n := mustFrom
	if n > len(s.opps) {
		n = len(s.opps)
	}
	type row struct {
		c, base cand
		r, br   res
		rounds  int
		filled  bool
		partial bool
	}
	var rows []row
	scoreTxt := fmt.Sprintf("score na %d zetten", s.M)
	if s.M == 13 {
		scoreTxt = "score over alle 13 zetten"
	}
	if fill && s.dl < 12 {
		budget := time.Duration(seconds) * time.Second / time.Duration(len(snap))
		if budget < 5*time.Second {
			budget = 5 * time.Second
		}
		for i, it := range snap {
			fmt.Printf("\rOpvullen van engine %d/%d (%s)...%40s", i+1, len(snap), it.c.String(), "")
			fc, fr, complete := s.fillSearch(it.c, threads, budget)
			rows = append(rows, row{c: fc, base: it.c, r: fr, br: it.r, rounds: 13, filled: true, partial: !complete})
		}
		fmt.Printf("\r%70s\r", "")
		sort.SliceStable(rows, func(i, j int) bool { return rows[i].r.val() > rows[j].r.val() })
		fmt.Printf("\nBeste engines tegen %d tegenstanders, opgevuld tot 12 zetten (score over alle 13 zetten):\n", n)
	} else {
		for _, it := range snap {
			rows = append(rows, row{c: it.c, base: it.c, r: it.r, br: it.r, rounds: s.M})
		}
		fmt.Printf("\nBeste engines tegen %d tegenstanders, %s:\n", n, scoreTxt)
	}
	totLoss, totScore := 0, 0
	for i, rw := range rows {
		kind := "diepte-engine"
		if k := letterRun(rw.base); k > 0 {
			kind = fmt.Sprintf("combinatie (%d vaste zetten + diepte)", k)
		}
		fmt.Printf("  %d. %-13s verliest %d | wint %d | gelijk %d | score %d   [%s]\n",
			i+1, rw.c.String(), rw.r.losses, rw.r.wins, rw.r.draws, rw.r.score, kind)
		if rw.filled {
			note := ""
			if rw.partial {
				note = " (aanvulling niet volledig doorzocht: tijd op)"
			}
			fmt.Printf("     beste %d zetten: %s (na %d zetten: verliest %d, score %d); aanvulling: %s%s\n",
				s.dl, rw.base.String(), s.dl, rw.br.losses, rw.br.score, rw.c.String()[s.dl:], note)
		}
		lose, notWon := losersOf(rw.c, s.opps, rw.rounds)
		if len(notWon) > 0 {
			var ls []string
			for _, idx := range notWon {
				ls = append(ls, names[idx])
			}
			fmt.Printf("     WAARSCHUWING: wint niet van must-win engine(s): %s\n", strings.Join(ls, ", "))
		}
		if len(lose) > 0 {
			var ls []string
			for j, idx := range lose {
				if j >= 6 {
					ls = append(ls, fmt.Sprintf("... (+%d)", len(lose)-6))
					break
				}
				ls = append(ls, names[idx])
			}
			fmt.Printf("     verliest van: %s\n", strings.Join(ls, ", "))
		}
		totLoss += rw.r.losses
		totScore += rw.r.score
	}
	fmt.Printf("Gemiddeld: %.2f verloren matches, score %.1f per engine.\n", float64(totLoss)/float64(len(rows)), float64(totScore)/float64(len(rows)))
	fmt.Println()
}

// ---------- opvullen tot 12 zetten ----------
//
// Na de zoektocht naar de beste zetten worden de zetten dl+1..12 aangevuld met cijfers (makkelijke dieptes):
// maximaal maxFillRuns reeksen van gelijke cijfers, bv. 11123 en 112211 (beide 3 reeksen). Voor elke engine
// wordt de beste aanvulling gekozen op basis van het volledige spel (alle 13 zetten tellen mee voor de score).

const maxFillRuns = 3 // maximaal 3 reeksen: 11123 (111,2,3) en 112211 (11,22,11) zijn beide 3 reeksen

type fillNode struct {
	pos   int
	last  byte // laatste cijfer van de aanvulling (0 = nog niets)
	runs  int  // aantal reeksen tot nu toe
	used5 bool
}

func (n fillNode) children(out []byte) []byte {
	out = out[:0]
	for d := byte('1'); d <= depthMax; d++ {
		if d == '5' && n.used5 {
			continue
		}
		if n.last != 0 && d != n.last && n.runs >= maxFillRuns {
			continue
		}
		out = append(out, d)
	}
	return out
}

func (n fillNode) next(ch byte) fillNode {
	n.pos++
	if ch != n.last {
		n.runs++
		n.last = ch
	}
	if ch == '5' {
		n.used5 = true
	}
	return n
}

type fillWorker struct {
	s      *searcher
	levels [][]ost
	buf    [13]byte
	best   res
	bestC  cand
	have   bool
}

func (w *fillWorker) rec(n fillNode, cur []ost, stop *atomic.Bool) bool {
	if n.pos == 12 {
		r := evalLeaf(cur, w.s.opps, true)
		if !w.have || r.val() > w.best.val() {
			w.best, w.have = r, true
			w.bestC = cand{b: w.buf, n: 12}
		}
		return true
	}
	if n.pos < 11 && stop.Load() {
		return false
	}
	var chBuf [16]byte
	nxt := w.levels[n.pos+1]
	for _, ch := range n.children(chBuf[:0]) {
		for j := range cur {
			stepOpp(n.pos, ch, &cur[j], &nxt[j], &w.s.opps[j])
		}
		w.buf[n.pos] = ch
		if !w.rec(n.next(ch), nxt, stop) {
			return false
		}
	}
	return true
}

// fillSearch kiest de beste aanvulling (cijfers) voor een engine van dl zetten. complete = alles doorzocht.
func (s *searcher) fillSearch(base cand, threads int, budget time.Duration) (cand, res, bool) {
	root := fillNode{pos: s.dl}
	for i := 0; i < s.dl; i++ {
		if base.b[i] == 'D' || base.b[i] == '5' {
			root.used5 = true
		}
	}
	cutLen := s.dl + 3
	if cutLen > 12 {
		cutLen = 12
	}
	var tasks [][]byte
	var gen func(n fillNode, cur []byte)
	gen = func(n fillNode, cur []byte) {
		if n.pos == cutLen {
			tasks = append(tasks, append([]byte(nil), cur...))
			return
		}
		for _, ch := range n.children(nil) {
			gen(n.next(ch), append(cur, ch))
		}
	}
	gen(root, nil)

	var stop atomic.Bool
	timer := time.AfterFunc(budget, func() { stop.Store(true) })
	defer timer.Stop()
	var next, done atomic.Int64
	var mu sync.Mutex
	var best res
	var bestC cand
	have := false
	var wg sync.WaitGroup
	for t := 0; t < threads; t++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			w := &fillWorker{s: s, levels: make([][]ost, 13)}
			for i := range w.levels {
				w.levels[i] = make([]ost, len(s.opps))
			}
			for j := range w.levels[0] {
				w.levels[0][j] = ost{av: [5]int{3, 3, 3, 3, 1}, bv: [5]int{3, 3, 3, 3, 1}}
			}
			for i := 0; i < s.dl; i++ { // de gekozen engine afspelen
				for j := range w.levels[i] {
					stepOpp(i, base.b[i], &w.levels[i][j], &w.levels[i+1][j], &s.opps[j])
				}
				w.buf[i] = base.b[i]
			}
			for !stop.Load() {
				ti := int(next.Add(1) - 1)
				if ti >= len(tasks) {
					break
				}
				n := root
				for _, ch := range tasks[ti] {
					for j := range w.levels[n.pos] {
						stepOpp(n.pos, ch, &w.levels[n.pos][j], &w.levels[n.pos+1][j], &s.opps[j])
					}
					w.buf[n.pos] = ch
					n = n.next(ch)
				}
				if w.rec(n, w.levels[n.pos], &stop) {
					done.Add(1)
				}
			}
			if w.have {
				mu.Lock()
				if !have || w.best.val() > best.val() {
					best, bestC, have = w.best, w.bestC, true
				}
				mu.Unlock()
			}
		}()
	}
	wg.Wait()
	if !have {
		st := base.strat()
		return base, evaluate(&st, s.opps, 13), false
	}
	return bestC, best, int(done.Load()) == len(tasks)
}

// human toont een aantal als getal onder 1000, anders als k / M / G (nooit meer dan 1000 ervoor): 5k, 2M, 2G.
func human(v float64) string {
	switch {
	case v >= 1e9:
		return fmt.Sprintf("%dG", int(v/1e9))
	case v >= 1e6:
		return fmt.Sprintf("%dM", int(v/1e6))
	case v >= 1e3:
		return fmt.Sprintf("%dk", int(v/1e3))
	}
	return fmt.Sprintf("%d", int(v))
}

func letterRun(c cand) int {
	k := 0
	for k < c.n && isMoveLetter(c.b[k]) {
		k++
	}
	return k
}

func main() {
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 1024*1024), 1024*1024)

	fmt.Println("=== perfectplan: zoek de beste engines tegen jouw tegenstanders ===")
	cpus := runtime.NumCPU()
	threads := askInt(sc, fmt.Sprintf("Aantal cores gebruiken (1-%d)", cpus), cpus, 1, cpus)
	avail := availableMemMB()
	defMem := avail / 2
	if defMem > 4096 {
		defMem = 4096
	}
	if defMem < 256 {
		defMem = 256
	}
	memMB := askInt(sc, fmt.Sprintf("Geheugen in MB (beschikbaar ~%d MB)", avail), defMem, 64, 1<<20)
	seconds := askInt(sc, "Maximale zoektijd in seconden", 30, 1, 86400)
	runtime.GOMAXPROCS(threads)
	debug.SetMemoryLimit(int64(memMB) * 1024 * 1024)

	for {
		fmt.Println("\nVoer de tegenstander-engines in (één per regel, '@bestand.txt' om een bestand te laden, '.' of lege regel om te stoppen):")
		engines, names := readEngines(sc)
		if len(engines) == 0 {
			fmt.Println("Geen engine codes ingevoerd. Gestopt.")
			return
		}
		// must-win engines: daar moet altijd van gewonnen worden
		mustCount := 0
		fmt.Print("Zijn er must win engines bij? (j/n, default n): ")
		if sc.Scan() {
			if t := strings.ToLower(strings.TrimSpace(sc.Text())); t == "j" || t == "ja" || t == "y" {
				fmt.Println("Plak de must-win engine codes (één per regel, '.' of lege regel om te stoppen):")
				me, mn := readEngines(sc)
				engines = append(engines, me...)
				names = append(names, mn...)
				mustCount = len(me)
			}
		}
		// dieptes: bij n worden alleen 1-5 gezocht (6-9 komen dan nooit in de gevonden engines voor)
		depthMax = '9'
		fmt.Print("Dieptes uitgebreid (1-9)? j = 1-9, n = alleen 1-5 (default j): ")
		if sc.Scan() {
			if t := strings.ToLower(strings.TrimSpace(sc.Text())); t == "n" || t == "nee" {
				depthMax = '5'
			}
		}
		moves := askInt(sc, "Hoeveel zetten spelen (1-12; bij 12 telt de laatste automatische zet ook mee)", 12, 1, 12)
		prefix := askPrefix(sc, moves)
		letterCount := -1
		if strings.Trim(prefix, "WVALD") == "" {
			letterCount = askLetterCount(sc, len(prefix), moves)
		}
		size := askInt(sc, "Hoeveel engines zoeken?", 3, 1, 1000)
		fill := false
		if moves < 12 {
			fill = askFill(sc)
		}

		opps := make([]strat, len(engines))
		for i, e := range engines {
			opps[i] = newStrat(e)
		}
		fmt.Printf("%d tegenstanders", len(opps)-mustCount)
		if mustCount > 0 {
			fmt.Printf(" + %d must-win engines (altijd winnen)", mustCount)
		}
		fmt.Printf(", zoeken naar %d engines voor %d zetten", size, moves)
		if prefix != "" {
			fmt.Printf(" met beginzetten %s", prefix)
		}
		fmt.Printf(" (%d cores, %d MB, max %ds)...\n", threads, memMB, seconds)
		run(opps, names, mustCount, prefix, moves, letterCount, fill, size, threads, memMB, seconds)
	}
}
