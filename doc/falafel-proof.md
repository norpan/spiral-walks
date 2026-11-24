# The Falafel walk never ends (A399160)

The proof by hand and by program, as of 23 Nov 2026, with a section on the Lean proof.

The Falafel (Fers + Alfil) is never trapped. This is proved in Lean 4 and checked by the Lean kernel,
together with three more facts: the rule allows only one walk, the walk visits every square of its
colour, and every odd positive integer is a term exactly once. So the sequence is a permutation of
the odd positive integers. After its first 79 steps the walk repeats one lap pattern forever, with only the lengths
growing. The argument by hand and by program further down came first. It shows why the pattern holds,
and the result no longer depends on it.

## Coordinates

Put u = (x + y)/2 and v = (x − y)/2.

- **Squares.** The Falafel only stands on squares with x + y even, and these are exactly the integer
  points (u, v).
- **Moves.** Its moves become (±1, 0), (0, ±1), (±2, 0) and (0, ±2): a rook limited to 1 or 2 squares.
- **Rings.** Ring r of the spiral becomes the diamond |u| + |v| = r. Within a ring the numbering starts
  just after (0, r), runs through (r, 0), (0, −r) and (−r, 0), and ends at (0, r).

All coordinates below are (u, v).

## The formula

The first 80 terms end on the square (2, 4). From there the walk is a sequence of laps R = 4, 5, 6,
and so on. Lap R starts on (2, R) if R is even and on (4, R − 1) if R is odd, and makes these moves
in order:

| Stretch | Moves | Number of moves |
| --- | --- | --- |
| 1. Top | Even R: (−2, 0), (1, 0), (−2, 0). Odd R: (−1, 0), (0, 1), (−2, 0) | 3 |
| 2. West run | (−1, 0) repeated | R − 2 for even R, R for odd R |
| 3. Staircase | (0, −1), (−1, 0) alternating | 2(R − 2) |
| 4. West corner | (0, −2), (0, −1), (0, 2), (−1, 0), (0, −1), (0, −1) | 6 |
| 5. Staircase | (0, −1), (1, 0) alternating | 4R − 7 |
| 6. South corner | (2, 0), (1, 0), (−2, 0), (0, −1), (1, 0), (1, 0) | 6 |
| 7. Staircase | (1, 0), (0, 1) alternating | 4R − 5 |
| 8. East corner | (0, 2), (0, 1), (0, −2), (1, 0), (0, 1), (0, 1) | 6 |
| 9. Staircase | (0, 1), (−1, 0) alternating | R + 1 |
| 10. Descent | Even R: (−2, 0), (−1, 0), (0, 1) repeating. Odd R: (−2, 0), (0, 1), (−1, 0) repeating | 3R/2 − 5 for even R, (3R − 5)/2 for odd R |

Lap R has 13.5R − 1 moves for even R and 13.5R + 3.5 for odd R, and it ends on the start square of
lap R + 1.

- **What a lap does.** Stretch 2 fills one row, v = R, of an unvisited triangle at the top left.
  Stretches 3 to 9 add two rings around the other sides. Stretch 10 fills one slanted strip of an
  unvisited triangle at the top right.
- **Shape.** The lowest unvisited ring is therefore about R while the outermost visited ring is about
  2R. This is the factor 2 seen in the run.

## Theorem

For every R ≥ 4 the walk performs lap R exactly as in the table. Every lap is finite and leads into
the next, so the walk never ends and A399160 is infinite.

## Proof in Lean

The result is proved in Lean 4.36 with Mathlib, in the folder `lean`. The Lean kernel checks every step. The proof has no `sorry` and no `native_decide`. It depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Theorem in Lean | What it says |
| --- | --- |
| `never_trapped` | There is an infinite sequence that follows the rule of the walk. So the walk is never trapped. |
| `deterministic` | Two sequences that follow the rule are equal. So the rule allows only one walk. |
| `visits_exactly_even_squares` | The walk visits every square (x, y) with x + y even, and no other square. |
| `permutation_of_odd_numbers` | Every term is an odd positive integer, and every odd positive integer is a term exactly once. So the sequence is a permutation of the odd positive integers. |
| `walk_follows_path` | In every lap R ≥ 4 the walk runs through the closed-form squares of the Lean model, in order. |
| `lapnum_eq_iff` | Exact cover. For R ≥ 4 the squares with lap number R are exactly the closed-form squares of lap R. |
| `lapnum_le_three_iff` | The squares with lap number at most 3 are exactly the first 80 squares of the walk. |
| `first_terms` | The first 70 terms of the walk are the 70 terms in the DATA section of A399160. |

The first four are stated with the definitions at the end of this section only. They are the four claims of the statement. Each is one statement of the paper version of this proof: Remark 1, Theorem 1 (a), Theorem 1 (b) and Corollary 8. The last four also use the Lean model: its lap number and its closed-form squares. The walk cannot reach a square with x + y odd, because every move keeps x + y even. In Lean this is the second half of `visits_exactly_even_squares`.

**Odd numbers.** Three lemmas hold for every square (x, y), not only for the Falafel's squares. The spiral number is positive. It is odd exactly when x + y is even. Every positive integer is the number of some square. So an odd positive integer is the number of a square with x + y even. The walk visits that square, and it visits no square twice.

**How it differs from the proof below.**

- **All laps at once.** It covers every lap R ≥ 4 directly. No lemma has a bound on R, and nothing is checked on some laps and then extended. Section 3 is not used.
- **Stamps.** Every square (u, v) gets a stamp, which is its lap number and an index within the lap. It also gets a move.
- **Five facts.** They are proved for all squares of all laps, by cases on the region of the square. The index is in range. Different squares have different stamps. The move leads to the next stamp. The move is a rook move of 1 or 2. A neighbour with a later stamp has no lower number than the square moved to.
- **First 80 squares.** They are a table. The same facts are checked for each of them by evaluation in the kernel.
- **Induction.** The stamp goes up one position per step. So after any step the visited squares are exactly those with stamps up to the current one. With the last of the five facts this gives the rule of the walk.

**Checked by program, not proved in Lean.**

- The lap number of the Lean model is the L of section 4. They are equal for all squares with |u|, |v| ≤ 400.
- The closed-form squares of the Lean model are the squares given by the move table above. They are equal for laps 4 to 400.

So the theorem above, in the form "as in the table", rests on the Lean proof and on this program check. That the walk never ends does not rest on it.

**The statement.** A reader has to trust only the definitions below, which are the file `Statement.lean`. `IsWalk a` says that a 0, a 1, a 2, … is an infinite run of the walk. The file also holds the 5 by 5 picture of the spiral from the OEIS page, as a checked example. All four claims were approved on 23 Nov 2026. On 24 Nov 2026 the third and fourth claim were completed, so that the four claims match the paper item by item. That text was approved the same day. No one outside this project has read it.

```lean
/-- The number of the square (x, y) on the square spiral, as OEIS has it: 1 at (0, 0),
2 at (1, 0), 3 at (1, 1), then counter-clockwise. Here `r` is the ring max(|x|, |y|),
and ring r ≥ 1 holds the numbers (2r - 1)² + 1 to (2r + 1)². -/
def spiral (p : ℤ × ℤ) : ℤ :=
  let x := p.1
  let y := p.2
  let r := max |x| |y|
  if x = r ∧ y > -r then (2 * r - 1) ^ 2 + (y + r)        -- right side, going up
  else if y = r then (2 * r - 1) ^ 2 + 2 * r + (r - x)    -- top side, going left
  else if x = -r then (2 * r - 1) ^ 2 + 4 * r + (r - y)   -- left side, going down
  else (2 * r - 1) ^ 2 + 6 * r + (x + r)                  -- bottom side, going right

/-- The Falafel (Fers + Alfil) moves one or two squares diagonally. -/
def IsMove (p q : ℤ × ℤ) : Prop :=
  |q.1 - p.1| = |q.2 - p.2| ∧ (|q.1 - p.1| = 1 ∨ |q.1 - p.1| = 2)

/-- `a 0, a 1, a 2, ...` is an infinite run of the walk. It starts on square 1 and visits no
square twice. Each next square is one move away. Every square one move away with a lower number
than the next square was visited before. -/
structure IsWalk (a : ℕ → ℤ × ℤ) : Prop where
  start : a 0 = (0, 0)
  injective : Function.Injective a
  move : ∀ n, IsMove (a n) (a (n + 1))
  lowest : ∀ n q, IsMove (a n) q → spiral q < spiral (a (n + 1)) → ∃ m ≤ n, a m = q

/-- Remark 1. The rule decides every step: there is at most one infinite run. -/
def Deterministic : Prop := ∀ a b : ℕ → ℤ × ℤ, IsWalk a → IsWalk b → a = b

/-- Theorem 1 (a). The walk is never trapped: it has an infinite run.
A399160(n) is `spiral (a (n - 1))`. -/
def NeverTrapped : Prop := ∃ a : ℕ → ℤ × ℤ, IsWalk a

/-- Theorem 1 (b). The walk visits every square (x, y) with x + y even, and no other square. -/
def VisitsExactlyEvenSquares : Prop :=
  ∀ a : ℕ → ℤ × ℤ, IsWalk a → ∀ x y : ℤ, (∃ n, a n = (x, y)) ↔ Even (x + y)

/-- Corollary 8. Every term is an odd positive integer, and every odd positive integer is a term
exactly once. So A399160 is a permutation of the odd positive integers. -/
def PermutationOfOddNumbers : Prop :=
  ∀ a : ℕ → ℤ × ℤ, IsWalk a →
    (∀ n, 0 < spiral (a n) ∧ Odd (spiral (a n))) ∧
    (∀ k : ℤ, 0 < k → Odd k → ∃! n, spiral (a n) = k)
```

## Proof by hand and by program

This is the argument from before the Lean proof. The Lean proof does not use it. It is kept because it shows where the lap pattern comes from.

### 1. The move is decided locally

The next square is the lowest-numbered unvisited one among the 8 neighbours. It is determined by which
neighbours are visited and by the order of their numbers.

### 2. Four finite checks, done by program

| Check | Statement | Result |
| --- | --- | --- |
| A | The squares given by the formula, that is the first 80 terms and laps 4 to 300, are pairwise distinct | 609,893 squares, all distinct |
| B | Taking as visited exactly the formula's earlier squares, every step of laps 4 to 296 goes to the lowest-numbered unvisited neighbour | 593,689 steps, no exception |
| C | See below | 4,056 cases, all stable |
| D | The facts behind section 3, items 3 to 5, over laps 12 to 296 (extend.py): within an address each neighbour's quadrant, and whether a neighbour in the same stretch is visited first, are fixed and do not drift as R grows; the set of addresses repeats every 12 laps; key gives the spiral order | 4,056 and 1,189 pairs stable; no new address in laps 297 to 3000 |

For check C, give each step an address: the parity of R, its stretch, its distance from the start of
the stretch if below 8, its distance from the end if below 8, and its index in the stretch modulo 6.
For laps 12 to 296:

- steps with the same address have the same local picture;
- each of the 8 neighbours is visited by the same stretch of lap R − d, with the same d between −2
  and 3;
- within that stretch the neighbour sits at a fixed distance from the start, or a fixed distance from
  the end, or a fixed distance from the current step's own index, and in the last case the two
  stretches grow by the same amount per 12 laps;
- no neighbour lies in the first 80 terms.

Independently, the formula agrees with a direct simulation of the walk for laps 4 to 666, which is
steps 80 to 2,999,324.

### 3. From 300 laps to all laps

1. **Everything in the formula is affine up to a periodic part.** For each parity, the start square and the stretch lengths are affine in R. The displacement after i moves of a stretch is affine in i plus a term of period 1, 2 or 3. Shifting R by 12 changes every stretch length by a multiple of 6: by 0, 12, 24, 0, 48, 0, 48, 0, 12 and 18 for stretches 1 to 10. So once R is fixed modulo 12 and i modulo 6, the square reached after i moves of a given stretch of lap R is an affine function of (R, i). For a step at a fixed distance from the start of its stretch, i is a constant. For one at a fixed distance from the end, i is the stretch length minus a constant, which is affine in R.
2. **The equalities of check C hold for all R ≥ 12.** A relation of the form "the neighbour at this offset is the square at that position of that stretch of lap R − d" equates two functions of R and i that are affine on each class of R modulo 12 and i modulo 6 (item 1). For a step near either end of a stretch, both sides are affine in R alone, and agreement at two values of R in a class gives agreement for all. For a step in the middle, both sides are affine in (R, i), and agreement at three points not on a line gives agreement for all. Check C verifies every relation at every step of laps 12 to 296, which is at least 23 values of R in each class. So the relation holds for every R ≥ 12.
3. **The inequalities also hold for all R ≥ 12.** Item 2 extends equalities only. Three kinds of inequality are needed as well, and check D covers each.
   - *The source lies inside its stretch.* Every stretch length is non-decreasing in R, so a source at a fixed distance from the start or the end of its stretch stays inside it. For a source at a fixed offset from the current step, both stretches grow by the same amount per 12 laps. The margin then depends only on R modulo 12, and check C covers every class.
   - *Whether a neighbour was visited before the step.* It was exactly when its lap, stretch and index come earlier in the formula. If d ≠ 0, or the stretches differ, the address decides it. In the same stretch of the same lap it is the sign of i2 − i, the source's index minus the step's. Within an address the extremes of i2 − i are affine in R on each class modulo 12. Check D confirms for all 1,189 such pairs, over laps 12 to 296, that the sign is constant and the extremes do not move toward 0.
   - *The quadrant of each neighbour.* Item 4 needs it. Within an address, the smallest and largest u and v of a neighbour are taken at the ends of an interval of i whose end points are affine in R, so they are affine in R on each class modulo 12. Check D confirms for all 4,056 address and neighbour pairs, over laps 12 to 296, that the signs of u and v are constant and the extremes do not move toward an axis. So the signs stay fixed for every R.
4. **The order of the neighbours' numbers is the same within an address.** A square's number is fixed by its ring |u| + |v| and its position along the ring. Within each quadrant the position is affine in u and v. This is key in induct.py, and check D confirms that it gives the spiral order for |x|, |y| ≤ 60. With the quadrants fixed (item 3), the ring difference of two neighbours depends only on their offsets. On one ring and in one quadrant, so does their position difference. On one ring but in different quadrants, the order is that of the quadrants along the ring, whatever r is.
5. **Every address of a later lap has been seen.** Addresses depend only on the stretch lengths. From lap 23 on, every stretch that grows has at least 22 moves: 8 steps near each end and at least 6 in the middle, so every residue modulo 6 occurs in the middle. The set of addresses of a lap then depends only on the stretch lengths modulo 6, which repeat every 12 laps (item 1). So every address of a lap R ≥ 297 already occurs in laps 12 to 296, where checks B and C tested it. Check D confirms this up to lap 3000.
6. **Lemma (no overlap).** The squares of different laps, and of different steps of one lap, are distinct for all R. Section 4 proves it.
7. **Induction.** The first 80 terms are computed directly. Suppose the walk has followed the formula up to some step of lap R ≥ 4. Then the visited squares are exactly the formula's earlier squares. For laps 4 to 296, check B says the next step follows the formula. For R ≥ 12, let a be the step's address. By item 2 each neighbour is a definite square of the formula, at a known lap, stretch and index. By item 6 it is no other square of the formula, so it is visited exactly when that position comes earlier, and by item 3 this is as recorded for a. By items 3 and 4 the order of the neighbours' numbers is as recorded for a. By item 5, a occurred in laps 12 to 296, where it had a single picture, and check B shows that for this picture the formula's move is the lowest-numbered unvisited neighbour. So the next step follows the formula.

### 4. Proof of the lemma

The lemma is proved by giving every square a lap number that depends only on the square.

**Definition.** For a square (u, v) outside the centre block, where u and v are both between −1 and 1,
define L(u, v) by this table. The ten regions do not overlap, and together they cover everything
outside the centre block.

| Region | Condition | L(u, v) |
| --- | --- | --- |
| 1. North row | u ≤ 1, v ≥ 2, u + v ≥ 1 | v |
| 2. North-west | v ≥ 2, u + v ≤ 0 | ⌊(v − u)/2⌋ + 1 |
| 3. West corner | u ≤ −2, −1 ≤ v ≤ 1 | ⌊(3 − u)/2⌋ |
| 4. South-west | u ≤ −2, v ≤ −2 | ⌊(1 − u − v)/2⌋ |
| 5. South corner | −1 ≤ u ≤ 1, v ≤ −2 | ⌊(2 − v)/2⌋ |
| 6. South-east | u ≥ 2, v ≤ −2 | ⌊(u − v)/2⌋ |
| 7. East corner | u ≥ 2, −1 ≤ v ≤ 1 | ⌊(u + 1)/2⌋ |
| 8. North-east, lower part | u ≥ 2, v ≥ 2, u − 3v ≥ −6 | ⌊(u + v − 1)/2⌋ |
| 9. Column 3 | u = 3, v ≥ 2, u − 3v ≤ −7 | v if v is odd, v + 1 if v is even |
| 10. North-east, upper part | u ≥ 2, u ≠ 3, v ≥ 2, u − 3v ≤ −7 | Put s = u + 3v and take its remainder modulo 6. Remainder 0: s/3 − 2. Remainder 1 or 4: (s − 4)/3. Remainder 2: (s − 5)/3. Remainder 3: (s − 3)/3. Remainder 5: (s − 2)/3 |

**Claim.** For every R ≥ 4, every square visited in lap R has L = R.

To prove it, write the squares of lap R in closed form, read off the region and substitute. The start
square of a lap counts as the last square of the lap before it.

| Stretch | Squares, in order | Region | Why L = R |
| --- | --- | --- | --- |
| 1. Top, even R | (0, R), (1, R), (−1, R) | 1 | v = R |
| 1. Top, odd R | (3, R − 1), (3, R), (1, R) | 9, 9, 1 | R − 1 is even and R is odd; in the third square v = R |
| 2. West run | (u, R) for u from −2 (even R) or 0 (odd R) down to −(R − 1) | 1 | v = R |
| 3. Staircase | For k = 0, …, R − 3: (−(R − 1) − k, R − 1 − k), then (−R − k, R − 1 − k) | 2 | v − u is 2R − 2 or 2R − 1 |
| 4. West corner | u is −(2R − 3) or −(2R − 2), and −1 ≤ v ≤ 1 | 3 | 3 − u is 2R or 2R + 1 |
| 5. Staircase | For j = 1, …, 4R − 7: (−(2R − 2) + ⌊j/2⌋, −1 − ⌈j/2⌉) | 4 | 1 − u − v is 2R or 2R + 1 |
| 6. South corner | v is −(2R − 2) or −(2R − 1), and −1 ≤ u ≤ 1 | 5 | 2 − v is 2R or 2R + 1 |
| 7. Staircase | For j = 1, …, 4R − 5: (1 + ⌈j/2⌉, −(2R − 1) + ⌊j/2⌋) | 6 | u − v is 2R or 2R + 1 |
| 8. East corner | u is 2R − 1 or 2R, and −1 ≤ v ≤ 1 | 7 | u + 1 is 2R or 2R + 1 |
| 9. Staircase | For j = 1, …, R + 1: (2R − ⌊j/2⌋, 1 + ⌈j/2⌉) | 8 | u + v − 1 is 2R or 2R + 1 |
| 10. Descent, even R, with h = R/2 | For k = 0, …, h − 2: (3h − 3k − 2, h + 2 + k). For k = 0, …, h − 3 also (3h − 3k − 3, h + 2 + k) and (3h − 3k − 3, h + 3 + k) | 10 | s is 3R + 4, 3R + 3 or 3R + 6, with remainders 4, 3 and 0 |
| 10. Descent, odd R, with p = (3R − 1)/2 and w = (R + 3)/2 | For k = 0, …, (R − 3)/2: (p − 3k − 2, w + k) and (p − 3k − 2, w + k + 1). For k = 0, …, (R − 5)/2 also (p − 3k − 3, w + k + 1) | 10 | s is 3R + 2, 3R + 5 or 3R + 4, with remainders 5, 2 and 1 |

Each line is a direct substitution. Two of them need a remark about the region:

- **Stretch 9 stays in region 8.** Along the stretch u − 3v only decreases, and at the last square it
  is −6 for even R and −5 for odd R.
- **Stretch 10 stays in region 10.** At its first square u − 3v is −8 for even R and −7 for odd R, and
  it only decreases from there. The values of u are 4, 7, 10, … and 6, 9, 12, … for even R, and
  2, 5, 8, … and 4, 7, 10, … for odd R, so u is never 3.

**The lemma follows.**

- **Different laps.** A square has only one lap number, so a square of lap R is never a square of
  another lap.
- **The first 80 terms.** Each of the first 80 squares lies in the centre block or has L ≤ 3, which is
  a finite check done by program. So none of them is a square of a lap R ≥ 4.
- **Within one lap.** Different stretches lie in different regions, except that stretches 1 and 2
  share the row v = R, where their values of u differ. Within a stretch the closed forms give distinct
  squares. In stretches 5, 7 and 9 the pair ⌊j/2⌋, ⌈j/2⌉ determines j. In stretch 3 the value of v
  determines k, and the two squares with the same k differ in u. In the descent the three families
  have different s, and within a family v determines k.

**Program check.** `lapsquares.py` confirms for laps 4 to 1200, which is 9,729,513 squares, that the
closed forms above reproduce the move table of the formula, that every square lies in the region
stated, and that L = R.

**Observed here, proved in Lean since.** For laps 4 to 250 the squares with L = R are exactly the squares of lap R, and the squares in the centre block or with L ≤ 3 are exactly the first 80 squares. This section only observes it. The Lean proof now has it for every R, for the lap number and the closed-form squares of the Lean model: see "Proof in Lean". With the theorem, the Falafel visits every square of its colour.

## Status

- **Proved in Lean.** The walk never ends, the rule allows only one walk, the walk visits every square of its colour, and every odd positive integer is a term exactly once. Every term is odd, so the sequence is a permutation of the odd positive integers. Exact cover is proved for the Lean model. The Lean kernel checks the proof. See "Proof in Lean".
- **Trusted.** The statement of the Lean proof, which is 70 lines. All four claims were approved on 23 Nov 2026, and their present text on 24 Nov 2026. No one outside this project has read it.
- **Solid.** The formula, checks A to D, and the agreement with simulation over 3 million steps. All are reproducible with the scripts `lapcheck.py`, `induct.py`, `sources.py` and `extend.py`. The Lean model agrees with the move table for laps 4 to 400 and with L for |u|, |v| ≤ 400, by program.
- **Proved by hand, confirmed by program.** The lemma in section 4. The closed forms, regions and lap numbers are confirmed for laps 4 to 1200 by `lapsquares.py` and `lapnumber.py`. It was written in one sitting and nobody else has read it. The Lean proof has its own form of this lemma.
- **Reviewed once, not yet independently.** Section 3. A sceptical review found four gaps: item 2 gave the wrong reason, the inequalities were not covered, the item on the order of numbers was false as worded, and coverage of later addresses was not stated. They are closed above, with check D. The review was by Claude, which also wrote the proof, so an independent reader is still needed. The Lean proof does not use section 3, so the result no longer depends on it.
- **OEIS.** The entry for A399160 gives no formula and makes no statement about whether the sequence is finite.
