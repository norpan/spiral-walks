# The 32 pieces of Quest for Zero on the square spiral

Written 24 Nov 2026. Figures of the live runs were read from their logs on 25 Nov 2026 at 09:32.

Every proof named here is checked by Lean 4 (version 4.36.0, with Mathlib). The Lean project is
[`lean/`](../lean/); `lake build` in that folder checks all of it. A reader only has to
trust five short statement files, which are linked below.

## The question

- **Pieces.** The game Quest for Zero (https://bradspellman.com/q40/) has one piece for every
  combination of the five leapers W (0,1), F (1,1), D (0,2), N (1,2), A (2,2). That is 32 pieces:
  31 that can move, and the Zero, which has no leaper.
- **Walk.** The piece starts on square 1 of the square spiral and always moves to the lowest-numbered
  unvisited square it can reach. It is trapped when no such square exists.
- **Question per piece.** Is it ever trapped?

## Summary

| Status | Pieces | Count |
| --- | --- | --- |
| Never trapped, proved in Lean, easy | all 16 with W; D, DA; FD, FDA (Section "The easy pieces") | 20 |
| Never trapped, proved in Lean | F, A (Section "Ferz and Alfil"), FA (Section "Falafel") | 3 |
| Trapped, found by program | N, FN, AN, DN, FAN | 5 |
| Trapped at once | the Zero | 1 |
| Open | DAN, FDN, FDAN | 3 |

The Zero cannot move. Its walk is the single term 1: trapped at step 1 on square 1.

## All 32 pieces

The number is the piece's number in Quest for Zero. It is F = 1, W = 2, A = 4, D = 8, N = 16 added up. The Zero has number 0 and no leaper.

| No. | Q40 name | Other names | Leapers | OEIS | Result | Why, or basis |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | Zero | – | none | none | trapped at step 1 | it cannot move |
| 1 | Ferz | Fers | F | A316884 | never trapped | it walks round the diamonds abs(x) + abs(y) = 2k clockwise; the next square on the diamond always has a lower number than the squares further out (Lean) |
| 2 | Wazir | Vizir | W | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 3 | King | Man, Commoner, Guard | F W | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 4 | Alfil | Elephant (old), Fil | A | A317467 | never trapped | the Ferz walk at twice the size: diamonds abs(x) + abs(y) = 4k, clockwise (Lean) |
| 5 | Elephant (our Falafel) | Falafel (Betza), Ferfil (Jelliss), modern Elephant | F A | A399160 | never trapped | after its first 80 squares it walks laps 4, 5, 6, ..., each made of the same nine pieces; every square gets a lap and a place, and the rule always picks the next place (Lean) |
| 6 | Phoenix | Waffle (Betza), Caliph (Jelliss) | W A | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 7 | Prince Elephant | War Elephant | F W A | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 8 | Dabbaba | War Machine | D | A399158 | never trapped | the squares with both coordinates even, in increasing order, are one D move apart (Lean) |
| 9 | Fortress | Kirin (Chu shogi), Diamond (Jelliss) | F D | A005408 | never trapped | n and n+2 are one D or F move apart, so it walks 1, 3, 5, ... (Lean) |
| 10 | Machine | Wazaba, Woody Rook (Betza) | W D | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 11 | Warrior | Champion (Begnis) | F W D | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 12 | Alibaba | – | A D | A399158 | never trapped | the squares with both coordinates even, in increasing order, are one D move apart (Lean) |
| 13 | Alfilerzbaba | FAD (Betza), Feralfda | F A D | A005408 | never trapped | n and n+2 are one D or F move apart, so it walks 1, 3, 5, ... (Lean) |
| 14 | Master | Champion (Omega Chess) | W A D | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 15 | Pasha | Mastodon, Mammoth, Squire | F W A D | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 16 | Horse | Knight | N | A316667 | trapped at step 2016 | program |
| 17 | Priest | Prince (Jelliss), Dullahan (Knappen) | F N | A398717 | trapped at step 1051 | program |
| 18 | Emperor | Marquis (Scirocco) | W N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 19 | Centaur | Crowned Knight, Paladin | F W N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 20 | Kangaroo | Hospitaller (Jelliss), Priestess | A N | A398779 | trapped at step 59,677 | program |
| 21 | Leopard | High Priestess (Joyce) | F A N | A399167 | trapped at step 256,730,882 | program |
| 22 | Deer | – | W A N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 23 | Raccoon | – | F W A N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 24 | Carpenter | Templar (Jelliss), Scribe, Doughnut (Betza) | D N | A398965 | trapped at step 253,925,076 | program |
| 25 | Civet | – | F D N | A398194 | **open** | 1.364x10^13 steps without a trap |
| 26 | Minister | Duke (Musketeer Chess) | W D N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 27 | Cannon | – | F W D N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 28 | Squirrel | Castle, Bear, Centurion (Knappen) | A D N | A399315 | **open** | 1.499x10^13 steps without a trap |
| 29 | Spider | – | F A D N | A396103 | **open** | 1.424x10^13 steps without a trap |
| 30 | Elk | – | W A D N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |
| 31 | Lion | Lioness (Scirocco), Joker | F W A D N | A000027 | never trapped | n and n+1 are one W move apart, so it walks 1, 2, 3, ... (Lean) |

- The leapers are read from the Q40 page, where "up to two steps" means 1 or 2 steps.
- For A000027 and A005408 the OEIS entry is the plain sequence, not an entry about the piece.
  A399158 is titled for the Dabbaba only; the Alibaba has no entry of its own.
- Other names: a selection of names used elsewhere for exactly the same moves, from Wikipedia's
  "List of fairy chess pieces", Jelliss (mayhematics.com), the Chess Variant Pages and the rules
  of Scirocco. "–" means none was found in these sources, not that none exists. Several names
  mean other pieces for other authors (Champion is both 11 and 14; Prince is also the King's
  move; Duke and Emperor vary). Names reported only by Wikipedia: War Elephant, Champion (11),
  Dullahan, Doughnut, Duke, Castle, Bear, Centurion. "Civet" and "Spider" for these moves were
  not found outside Q40 and OEIS.

## 1. Never trapped: easy (20 pieces)

| Pieces | Walk | OEIS | Why | Basis |
| --- | --- | --- | --- | --- |
| The 16 pieces with W | 1, 2, 3, ... | A000027 | Squares n and n+1 are one W move apart. | Lean: [`StraightStatement.lean`](../lean/StraightStatement.lean), s = 1 |
| D (Dabbaba), DA (Alibaba) | 1, 11, 13, ..., 25, 51, ... | A399158 | The squares with both coordinates even, in increasing order. Each is one D move from the one before. | Lean: [`StraightStatement.lean`](../lean/StraightStatement.lean), s = 2 |
| FD (Fortress), FDA (Alfilerzbaba) | 1, 3, 5, ... | A005408 | Squares n and n+2 are one D move or one F move apart. The piece only reaches odd squares. | Lean: [`FortressStatement.lean`](../lean/FortressStatement.lean) |

- In each row the lowest unvisited square the piece can ever reach is always one move away.
- Checked by program: W, WF, WN, WA, WD, WFDNA for 20,000 terms; FD, FDA, D, DA for 200,000 terms.

## 2. Never trapped: proved (3 pieces)

| Piece | Q40 name | OEIS | Walk | Proof by hand | Lean statement | Lean proof |
| --- | --- | --- | --- | --- | --- | --- |
| F | Ferz | A316884 | Diamonds, clockwise | Section "Ferz and Alfil" | [`LeaperStatement.lean`](../lean/LeaperStatement.lean), s = 1 | [`Leaper/`](../lean/Leaper/) |
| A | Alfil | A317467 | The same diamonds, twice as large | Section "Ferz and Alfil" | [`LeaperStatement.lean`](../lean/LeaperStatement.lean), s = 2 | [`Leaper/`](../lean/Leaper/) |
| FA | Elephant (our Falafel) | A399160 | Laps of four staircases and three corners | Section "Falafel" and the [paper](falafel-paper/falafel-paper.pdf) | [`Statement.lean`](../lean/Statement.lean), [`PathStatement.lean`](../lean/PathStatement.lean) | [`Falafel/`](../lean/Falafel/) |

On 24 Nov 2026 none of the three OEIS entries said whether the walk ends.

## 3. Trapped (5 pieces)

| Piece | Q40 name | OEIS | Trapped at step | On square | Stated on OEIS |
| --- | --- | --- | --- | --- | --- |
| N | Horse | A316667 | 2016 | 2084 | yes |
| FN | Priest | A398717 | 1051 | 858 | yes |
| AN | Kangaroo | A398779 | 59,677 | 57,552 | yes |
| DN | Carpenter | A398965 | 253,925,076 | 259,115,490 | yes |
| FAN | Leopard | A399167 | 256,730,882 | 267,545,105 | proposed 23 Nov 2026, not yet approved |

All five were reproduced with the program `walk.c` on 24 Nov 2026. None is proved in Lean: a trap is a
finite computation, and the largest takes 2.6x10^8 steps.

## 4. Open (3 pieces)

| Piece | Q40 name | OEIS | Steps without a trap | Fewest unvisited moves on arrival | Squares skipped | Deepest gap |
| --- | --- | --- | --- | --- | --- | --- |
| DAN | Squirrel | A399315 | 1.499x10^13 | 2 (8,036 times) | 0 | 3 (30 times) |
| FDN | Civet | A398194 | 1.364x10^13 | 3 (3,302,233 times) | 0 | 2 |
| FDAN | Spider | A396103 | 1.424x10^13 | 6 (421,971,600 times) | 0 | 1 |

- **Fewest unvisited moves.** A trap is an arrival with 0. The count is how often the lowest value
  occurred.
- **Skipped.** A square that the walk can no longer visit. None so far, for any of the three.
- **Gap.** Take the squares straight inward from the square of arrival: those with the same y on
  the right and left sides of the ring, with the same x on the top and bottom sides. The gap is how
  many rings further in the lowest unvisited one of them lies. All 30 gaps of 3 are exactly 3; no
  gap of 4 has occurred.
- All of this is observed, not proved. The runs are still going.

## How the OEIS list was made

- The first 18 terms of each of the 15 pieces without W were searched on oeis.org.
- For every entry named above, our first 40 terms equal the entry's data.
- "Stated on OEIS" was read from the keyword `fini` and from comments that contain words such as
  "finite" or "trapped". Not every comment was read in full.

---

## The easy pieces

Wazir, Dabbaba and Alibaba first, then Fortress and Alfilerzbaba.

### Statement

Let s ≥ 1. Take any piece that can move s squares straight in each of the four directions and
whose moves all change both coordinates by multiples of s.

- s = 1: the Wazir, and every piece that has the Wazir's moves. These are the 16 pieces with W.
- s = 2: the Dabbaba, and the Alibaba (Dabbaba + Alfil).

**Theorem.** The walk of such a piece visits the squares with both coordinates multiples of s, in
increasing order of their numbers. Hence:

1. The piece is never trapped.
2. It visits every such square exactly once, and no other square.
3. The sequence is increasing. For s = 1 it is 1, 2, 3, ... (A000027).

So A399158 (Dabbaba) is infinite and increasing, its terms are the numbers of the squares with
both coordinates even, and the Alibaba makes the same walk.

### Proof

Ring r is the set of squares with max(|x|, |y|) = r. A square with both coordinates multiples of
s lies on a ring whose number is a multiple of s. Call these squares the lattice.

**Listed in increasing order, each lattice square is one straight move from the one before.**
Along ring sm the lattice squares sit s apart on each side, and the four corners are among them.
The last one on ring sm is the corner (sm, −sm), which is the last square of the ring. The first
one on ring s(m+1) is (s(m+1), −sm), one move to the right of that corner. The list starts with
(0, 0) and then (s, 0).

**So the rule follows the list.** Suppose the piece has visited exactly the first k squares of the
list. The next square of the list is one move away, and it is the lowest-numbered unvisited square
the piece can ever reach. So it is the lowest unvisited square one move away. ∎

### Fortress and Alfilerzbaba

Take any piece that has the moves of the Ferz and of the Dabbaba and whose moves all change x + y
by an even number. The Fortress (F + D) and the Alfilerzbaba (F + D + A) are such pieces.

**Theorem.** The walk of such a piece is 1, 3, 5, ... (A005408): term number n, counted from 0, is
2n + 1. So the piece is never trapped.

**Proof.** One step along the spiral changes the number by 1 and x + y by 1, and square 1 has
x + y = 0. So the odd squares are the squares with x + y even, and the piece never leaves them.
Squares n and n + 2 are two steps of the spiral apart. Two steps in a row go the same way or turn
a corner, so n + 2 is two squares straight from n (a Dabbaba move) or one square diagonally (a
Ferz move). So after 1, 3, ..., n the square n + 2 is one move away, and it is the lowest-numbered
unvisited square the piece can ever reach. ∎

### Status of this proof

- **Proved in Lean 4** (24 Nov 2026), for every s ≥ 1 and every such set of moves:
  [`Straight/`](../lean/Straight/), statement in
  [`StraightStatement.lean`](../lean/StraightStatement.lean) (57 lines). Four claims: the
  rule allows at most one walk; a walk exists; it visits exactly the squares with both
  coordinates multiples of s, with increasing numbers; a piece with the Wazir's moves has n-th
  term n. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.
- **Also in Lean:** the Wazir, the Dabbaba and the Alibaba as instances, and that the Dabbaba and
  the Alibaba make the same walk. The Lean proof takes the walk to be the spiral itself, scaled
  by s.
- **Checked by program:** for the Dabbaba and the Alibaba the walk by the rule equals the sorted
  list of the numbers of the squares with both coordinates even, for 200,000 terms.
- **Fortress and Alfilerzbaba, proved in Lean 4** (24 Nov 2026): [`Fortress/`](../lean/Fortress/),
  statement in [`FortressStatement.lean`](../lean/FortressStatement.lean) (42 lines), for
  every piece that has the moves of the Ferz and of the Dabbaba and whose moves all change x + y by
  an even number. Three claims: the rule allows at most one walk; a walk exists; its terms are
  1, 3, 5, .... The Lean proof takes the walk to be every second square of the spiral. Same
  axioms, no `sorry`, no `native_decide`.
- **Not done.** Nothing is posted on OEIS.

---

## Falafel

The Falafel (F + A) moves one or two squares diagonally. Its walk is OEIS A399160. The full proof
is the paper [`falafel-paper.pdf`](falafel-paper/falafel-paper.pdf); this section only states the
results and says how each is proved.

### Results

1. **Only one walk.** The rule allows at most one infinite walk.
2. **Never trapped.** An infinite walk exists.
3. **Squares.** The walk visits every square with x + y even, and no other square.
4. **Sequence.** Every term of A399160 is an odd positive integer, and every odd positive integer
   is a term exactly once. So A399160 is a permutation of the odd positive integers.
5. **Terms.** From its 81st term on the sequence is given by a formula. The walk runs in laps
   R = 4, 5, 6, ..., lap R starts with term number s(R) + 1, where s(R) = (27R² − 22R − 24)/4 for
   even R and (27R² − 22R − 33)/4 for odd R, so lap 4 starts with the 81st term. (The paper counts
   steps from 0, so there lap R starts at step s(R).) Within a lap every term is the square of an odd number plus a linear remainder. The
   table has 38 rows; it is Table 5 of the paper.

### How it is proved

With u = (x + y)/2 and v = (x − y)/2 the Falafel is a rook that moves one or two squares. After its
first 80 squares the walk runs in laps around the origin. Each lap is a row, three staircases with
a corner after each, a fourth staircase and a way back, and one closed formula gives the squares
of every lap. Every square gets a stamp: the number of its lap and its index within the lap. Four
lemmas about stamps carry the proof: the first 80 squares are a checked table; the formula and the
stamp are inverse to each other; the square with the next stamp is one move away; and no unvisited
square one move away has a lower number than it. Each lemma is a statement of linear integer
arithmetic, proved by a case analysis over the regions of the plane.

### Status

- **Proved in Lean 4** (23 and 24 Nov 2026). Results 1 to 4 are the four claims of
  [`Statement.lean`](../lean/Statement.lean) (70 lines), proved in
  [`Falafel/Theorems.lean`](../lean/Falafel/Theorems.lean). Result 5 is the claim of
  [`PathStatement.lean`](../lean/PathStatement.lean) (92 lines), proved in
  [`Falafel/Terms.lean`](../lean/Falafel/Terms.lean). Axioms: `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.
- **Also in Lean:** the first 70 terms of the walk are the DATA terms of A399160 (`first_terms`).
- **Checked by program:** the tables printed in the paper are transcriptions of the Lean
  definitions. The paper's build compares each with the Lean text and with a simulation of the
  rule for 200,000 steps before it writes the paper.
- **Not done.** Nothing is posted on OEIS.

---

## Ferz and Alfil

### Statement

Let s ≥ 1. The (s,s)-leaper moves from (x, y) to (x ± s, y ± s). The Ferz is s = 1, the Alfil is s = 2.

- **Reachable squares.** The squares (sp, sq) with p + q even.
- **Diamond k** (k ≥ 1). The reachable squares with |x| + |y| = 2ks. There are 8k of them. Every
  reachable square other than the origin lies on exactly one diamond.
- **Walking order of diamond k.** Clockwise from its first square (s, (2k−1)s) to its last square
  (0, 2ks): down-right to (2ks, 0), down-left to (0, −2ks), up-left to (−2ks, 0), up-right to (0, 2ks).

**Theorem.** The walk of the (s,s)-leaper visits the origin, then diamond 1, then diamond 2, and so
on, each in walking order. Hence:

1. The piece is never trapped.
2. It visits every reachable square exactly once.
3. Diamond k is terms 4k(k−1) + 2 to 4k(k+1) + 1 of the sequence.

**Corollaries.**

- A316884 (Ferz) is infinite and is a permutation of the odd positive integers. The Ferz reaches the
  squares with x + y even, and these are the squares with odd numbers.
- A317467 (Alfil) is infinite. Its terms are the numbers of the squares (2p, 2q) with p + q even,
  each exactly once.

### What is used about the spiral

Ring r is the set of squares with max(|x|, |y|) = r.

- **(S1)** A square on a smaller ring has a lower number.
- **(S2)** Within ring r the numbers go up counter-clockwise from (r, −r+1) to the corner (r, −r):
  up the right side, leftward along the top, down the left side, rightward along the bottom.

### Proof

The piece stands on a square P of diamond k. Assume it has visited the origin, all of diamonds
1 to k−1, and the squares of diamond k before P, and nothing else. We show that it moves to the
next square in walking order. Call that square Q.

**P inside a quadrant** (both coordinates non-zero). Of the four moves, one goes inward to diamond
k−1 or to the origin, which is visited. Two stay on diamond k: one to the square before P and one
to Q. One goes outward to a square O of diamond k+1. So Q must be compared with O. Write a, b > 0
for the absolute values of the coordinates of P.

| Quadrant | P | Q | O | If Q and O are on the same ring |
| --- | --- | --- | --- | --- |
| x > 0, y > 0 | (a, b) | (a+s, b−s) | (a+s, b+s) | Both on the right side, Q below O. |
| x > 0, y < 0 | (a, −b) | (a−s, −b−s) | (a+s, −b−s) | Both on the bottom side, Q left of O. |
| x < 0, y < 0 | (−a, −b) | (−a−s, −b+s) | (−a−s, −b−s) | Both on the left side, Q above O. |
| x < 0, y > 0 | (−a, b) | (−a+s, b+s) | (−a−s, b+s) | Both on the top side, Q right of O. |

In every row Q and O share one coordinate, and the other coordinate of Q is no larger in absolute
value. So the ring of Q is at most the ring of O. If it is smaller, Q has the lower number by (S1).
If the rings are equal, the shared coordinate is the ring number, and Q has the lower number by (S2).

**P the first square**, (s, (2k−1)s). The square before P in clockwise order is the last square
(0, 2ks), which is not yet visited. So Q = (2s, (2k−2)s) must also be compared with (0, 2ks), which
is on ring 2ks. For k ≥ 2, Q is on a smaller ring. For k = 1, Q = (2s, 0) is on the right side of
ring 2s and (0, 2s) is on its top side. Either way Q has the lower number.

**P on an axis, not the last square.** Take P = (2ks, 0). Two moves stay on diamond k: to
(2ks−s, s), which is visited, and to Q = (2ks−s, −s). The other two go to ring 2ks+s. Q is on ring
2ks−s, so Q has the lower number. The same holds at (0, −2ks) and (−2ks, 0).

**P the last square**, (0, 2ks). The two moves that stay on diamond k go to its first square and to
the square before P. Both are visited. The other two go to (s, 2ks+s) and (−s, 2ks+s). Both are on
the top side of ring 2ks+s, and (s, 2ks+s) is further right, so it has the lower number. It is the
first square of diamond k+1.

**Start.** From the origin the four moves go to the corners of ring s. The corner (s, s) has the
lowest number by (S2). It is the first square of diamond 1.

So the walk follows the diamonds for ever. This gives items 1 and 2. Item 3 follows by counting:
the origin and diamonds 1 to k have 1 + 4k(k+1) squares. ∎

### Status of this proof

- **Proved in Lean 4** (24 Nov 2026), for every s ≥ 1: [`Leaper/`](../lean/Leaper/), statement in
  [`LeaperStatement.lean`](../lean/LeaperStatement.lean) (50 lines). Four claims: the rule allows at most one walk; a walk
  exists (never trapped); it visits exactly the squares (s i, s j) with i + j even; for the Ferz,
  the sequence is a permutation of the odd positive integers. Axioms: `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.
- **Also in Lean:** the first 62 terms of the walk for s = 1 are the DATA terms of A316884, and
  the first 54 terms for s = 2 are those of A317467. `walk_eq_iff` gives the step at which each
  square is visited, which is item 3 above in another form.
- **Proved by hand.** The proof above. The Lean proof follows it: the table of quadrants and
  the axis cases are the lemmas `k2` to `k9` of [`Leaper/Greedy.lean`](../lean/Leaper/Greedy.lean).
- **Checked by program** (`ferz-alfil/check.py`, 7 s):
  - For s = 1, 2, 3 the walk by the rule equals the diamond path for 2,000,000 steps.
  - Every comparison of the proof holds on diamonds 1 to 400, for s = 1, 2, 3.
  - The term numbers of item 3 hold for k < 200.
- **Not done.** Nothing is posted on OEIS.
