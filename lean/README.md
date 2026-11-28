# lean: the Falafel walk (OEIS A399160) never ends, in Lean 4

Written Mon 23 Nov 2026. Lean v4.36.0 alone: no Mathlib, no other package. Until 28 Nov 2026 the
proofs used Mathlib v4.36.0; see "Without Mathlib" at the end.

## What is proved

Four theorems, in `Falafel/Theorems.lean`. Their statements are the four definitions at the
end of `Statement.lean`, in the same order. Since 24 Nov 2026 each is one full statement of the
paper (`doc/falafel-paper/`).

| Theorem | Paper | Statement |
| --- | --- | --- |
| `deterministic` | Remark 1 | Two sequences with `IsWalk` are equal: the rule decides every step. |
| `never_trapped` | Theorem 1 (a) | There is an infinite sequence `a` with `IsWalk a`: the walk is never trapped. |
| `visits_exactly_even_squares` | Theorem 1 (b) | A sequence with `IsWalk` visits a square (x, y) exactly if x + y is even. |
| `permutation_of_odd_numbers` | Corollary 8 | For a sequence with `IsWalk`, every term is an odd positive integer, and every odd positive integer is the spiral number of exactly one step. |

Until 24 Nov 2026 the third claim was `VisitsEveryEvenSquare` (only "every square with x + y even
is visited") and the fourth was `EveryOddNumberOnce` (without "every term is odd and positive",
which was the separate theorem `terms_odd_and_positive`).

- `lake build` succeeds. There is no `sorry`.
- `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for all four. These are the
  standard axioms of Lean.
- There is no `native_decide`. The finite checks use `decide`, which is evaluation inside the
  Lean kernel: the table of the first 80 squares (`Prefix.lean`), the first 70 terms
  (`Check.lean`), the picture in `Statement.lean`, and a few start values.
- Extra, not needed for the claim: `leanchecker` (a second run of the kernel over the compiled
  files) accepts every module that contains declarations. The tool itself crashes on some runs
  while loading files, before it checks anything, and always on the root module `Falafel`,
  which has no declarations. So it never rejected anything, but it is not one clean pass.
- All laps R ≥ 4 are covered directly. No lemma has a bound on R, and nothing is "checked up to
  a lap and then extended".

## What a reader must check

1. `Statement.lean`, 71 lines: the spiral number, the moves, `IsWalk`, and the four claims.
2. `Basic.lean`, 46 lines: the general notions the statement files use (`ℕ`, `ℤ`, `|x|`,
   `Even`, `Odd`, `∃!`, `Set`, `StrictMono`, `Function.update`), one line each. Mathlib has
   the same notions; here they are plain Lean. Nothing else has to be trusted.
3. That the four theorems in `Falafel/Theorems.lean` have those four claims as their types.
4. That the build prints the axiom lines above and no error.

Two things support the statement itself:

- `Statement.lean` contains the 5 by 5 picture of the spiral from the OEIS page as a checked
  example.
- `Falafel/Check.lean` proves that the first 70 terms of the walk are the 70 DATA terms of
  A399160 (fetched from oeis.org on 23 Nov 2026). With `deterministic` this ties `IsWalk` to
  the OEIS entry.

Martin approved the statement on 23 Nov 2026: the first three claims first, the fourth claim
later the same day. On 24 Nov 2026 he approved the present text, in which the third and fourth
claim are completed so that the four claims match the paper item by item.

## How the proof goes

It does not follow the write-up (`doc/falafel-proof.md`). There are no addresses and no step
from finitely many laps to all laps.

- **Coordinates.** u = (x + y)/2, v = (x - y)/2. The Falafel is a rook limited to 1 or 2 squares.
- **Model** (`Falafel/Model.lean`, `Falafel/Stamp.lean`). Every square (u, v) gets a stamp: a lap
  number and an index within the lap. It also gets a move. The first 80 squares are a table and
  count as lap 3.
- **Five facts about every square**, each proved for all laps at once by case analysis on the
  region of the square and `omega`:
  - the index is in the range of its lap (`pos_range`);
  - the closed-form path inverts (lap, index), so different squares have different stamps
    (`sq_pos`);
  - the move leads to the next stamp (`step_big`);
  - the move is a rook move of 1 or 2 (`rook_big`);
  - a neighbour with a later stamp has no lower spiral number than the square the walk moves to
    (`greedy_e1` to `greedy_s2`, one file per neighbour).
- **First 80 squares** (`Falafel/Prefix.lean`). The same facts, by evaluation.
- **Spiral order** (`Falafel/Spiral.lean`). The spiral number is (2 ring - 1)² + position, so
  comparing spiral numbers is comparing (ring, position).
- **Induction** (`Falafel/Main.lean`). The walk is the step applied n times from the origin, by recursion. Its stamps
  increase by one position per step. So after step n the visited squares are exactly the squares
  with stamp up to that of step n. With the greedy fact this gives `IsWalk`.
- **Odd numbers** (`Falafel/Numbers.lean`). Three facts about the spiral number of any square
  (x, y): it is positive (`spiral_pos`); it has the parity of x + y + 1 (`spiral_parity`); every
  positive integer is the spiral number of some square (`spiral_surjective`). So an odd positive
  integer is the number of a square with x + y even, the walk visits that square, and different
  steps have different numbers.

Two more results come out of this, in `Falafel/Main.lean`:

- **Exact cover**, which the write-up only observed: the walk visits the squares in the order of
  their stamps, so the squares with lap number R are exactly the squares visited in lap R.
- **`walk_follows_path`**: in every lap R ≥ 4 the walk runs through the closed-form path
  `(squ R j, sqv R j)` of `Model.lean` in order.
- **`walk_eq_path`** (`Falafel/Start.lean`): lap R ≥ 4 starts at step
  `start R` = (27R² − 22R − 24 − 9·(R mod 2))/4, so for `start R ≤ n < start (R + 1)` the n-th
  square is the square at index `lo R + (n − start R)` of that path.
- **`term_formula`** (`Falafel/Terms.lean`): the claim `TermFormula` of `PathStatement.lean`, a
  second statement file. It gives the number of the square at every step n ≥ 80 as a table of 38
  rows, each an odd square plus a linear remainder. This is Corollary 9 of the paper, and the
  table is its Table 6.
- **`lapnum_eq_iff`**: for R ≥ 4 the squares with lap number R are exactly the squares of that
  path. **`lapnum_le_three_iff`**: the squares with lap number at most 3 are exactly the first
  80 squares of the walk.

Checked in Python, not proved in Lean (`py/test_writeup.py`): the Lean path is the move table of
the write-up (laps 4 to 400), and the Lean lap number is the L of its section 4 (|u|, |v| ≤ 400).

## Build

Install Lean through [elan](https://github.com/leanprover/elan). Then, in this folder:

```
lake build Falafel Leaper Straight Fortress Trap
```

`lean-toolchain` fixes Lean v4.36.0. Nothing else is fetched: the project has no dependencies.
`lake build` alone builds only `Falafel`.

Measured on 28 Nov 2026 on a laptop that was running another job at the same time: a clean
build of the five libraries took 8 min 14 s wall (23 min of CPU), most of it `Trap/Kangaroo`
(450 s) and `Trap/Big` (257 s). Disk: Lean itself takes 3.0 GB and the folder `.lake` 161 MB.

## Files

| Path | What it is |
| --- | --- |
| `Statement.lean` | The statement. |
| `Basic.lean` | The general notions of the statement files, in place of Mathlib. Trusted with the statement. |
| `PathStatement.lean` | Second statement file: the table of terms and the claim that it gives the sequence. |
| `Falafel/Theorems.lean` | The four theorems. |
| `Falafel.lean` | Root of the library, with `#print axioms`. |
| `Falafel/Model.lean` | Lap number, index, move, closed-form path, ring and position, in (u, v). |
| `Falafel/Stamp.lean` | Table of the first 80 squares; lap, index and step for every square. |
| `Falafel/Tactic.lean` | `split_cases`, `split_omega`: split on `if`, drop impossible cases, `omega`. |
| `Falafel/Laps.lean`, `Step.lean` | Range, rook move, inverse map, next stamp, for laps R ≥ 4. |
| `Falafel/Greedy/*.lean`, `Greedy.lean` | The greedy fact for each of the 8 neighbours, for laps R ≥ 4. |
| `Falafel/Prefix.lean` | The first 80 squares, by evaluation. |
| `Falafel/Squares.lean` | The facts for all squares. |
| `Falafel/Spiral.lean` | Spiral numbers in (u, v). |
| `Falafel/Numbers.lean` | Spiral numbers of all squares: positive, parity, every positive integer occurs. |
| `Falafel/Main.lean` | The walk, the induction, uniqueness, every even square, every odd number once. |
| `Falafel/Start.lean` | The step at which each lap starts. |
| `Falafel/Terms.lean` | Proof of the term table: ring and position of every square of a lap, one case per row. |
| `Falafel/Check.lean` | The first 70 terms against the OEIS data. |
| `py/` | Python tests, see below. Not part of the proof. |

## Python tests (not proof)

They were used to get the definitions right before Lean saw them. They read the definitions out
of the Lean files, so they test the text that Lean checks.

```
python3 py/test_statement.py        Statement.lean mirrored by hand: OEIS picture, 70 terms, deviations rejected,
                                    3000 terms odd and distinct
python3 py/test_lemmas.py 300 300000   every lemma statement on the box |u|, |v| <= 300; exact cover and the
                                    write-up's closed forms for laps 4 to 148; the walk against a simulation
python3 -B py/test_writeup.py 400 400  the Lean lap number and path against the write-up's L and move table
```

All three pass. The second takes 6 s.

## Not done

- The proof files have had no reader other than the Lean kernel and Claude. The kernel checks
  the proof. Only a person can check that `Statement.lean` says what is meant; Martin has
  approved it, nobody else has read it.

## Second library: `Leaper` (Ferz and Alfil), 24 Nov 2026

The same Lake project holds a second library for the (s, s)-leaper: the Ferz is s = 1
(OEIS A316884) and the Alfil is s = 2 (OEIS A317467). Build it with `lake build Leaper`.

- **Statement:** `LeaperStatement.lean`, 50 lines. It uses `Falafel.spiral` of `Statement.lean`.
  The condition s > 0 is inside the three general claims. Martin approved it on 24 Nov 2026.
- **Theorems** (`Leaper/Theorems.lean`), the first three for every s > 0:
  `deterministic`, `never_trapped`, `visits_exactly_reachable_squares`,
  `ferz_permutation_of_odd_numbers`.
- **Check** (`Leaper/Check.lean`): the first 62 terms for s = 1 and the first 54 for s = 2 are
  the DATA terms of the two OEIS entries, by `decide +kernel`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

How the proof goes (`doc/pieces.md` has it for human readers):

- `Leaper/Spiral.lean`: spiral number = (2 ring - 1)² + position, for all squares.
- `Leaper/Model.lean`: the path of the (1, 1)-leaper round the diamonds |p| + |q| = 2k: next
  square, place on the diamond, and the rank `rk` (the step at which a square is reached). The
  next square has rank + 1, and the rank determines the square.
- `Leaper/Greedy.lean`: a diagonal neighbour that does not come before a square on the path has
  no lower spiral number than the next square, after scaling by s. The leap length enters only
  through sign facts about s p and s q, so everything is linear and `omega` closes it.
- `Leaper/Main.lean`: the walk is the path scaled by s; it satisfies `IsWalk s` and is unique.

## Wazir, Dabbaba, Alibaba: pieces that can move straight

A third library, `Straight`, in the same Lake project. Build it with `lake build Straight`
(2 min 25 s wall on 24 Nov 2026, with three other jobs running; nearly all of it is one case
analysis, `nxt_key`).

- **Statement:** `StraightStatement.lean`, 58 lines. A piece is a set `M` of moves. The
  condition `MovesStraight s M` says that the piece can move s squares straight in each of the
  four directions and that all its moves change both coordinates by multiples of s. It uses
  `Falafel.spiral` of `Statement.lean`.
- **Theorems** (`Straight/Theorems.lean`), for every s > 0 and every such `M`:
  `deterministic`, `never_trapped`, `visits_lattice_in_order` (the walk visits exactly the
  squares with both coordinates multiples of s, and its numbers increase), and
  `wazir_walks_in_order` (for s = 1 the n-th term is n).
- **Instances:** `wazir_never_trapped`, `dabbaba_never_trapped` (OEIS A399158),
  `alibaba_never_trapped`, and `alibaba_eq_dabbaba` (the two make the same walk). With s = 1 the
  theorems cover all 16 pieces that have the Wazir's moves.
- **How the proof goes** (`Straight/Main.lean`): `nx`, `ny` give the square after (x, y) along
  the spiral, and `spiral_nxt` says its number is one more. So the spiral itself is a sequence
  `w` with `spiral (w n) = n + 1`. Scaling by s multiplies ring and position by s (`rg_scale`,
  `ps_scale`), so it keeps the order of the numbers (`scale_lt`). The walk is s times `w`. It
  reuses `Leaper/Spiral.lean`.

## Fortress and Alfilerzbaba: the walk 1, 3, 5, ...

A fourth library, `Fortress`, in the same Lake project. Build it with `lake build Fortress`
(33 s wall on 24 Nov 2026, with three other jobs running and `Straight` already built).

- **Statement:** `FortressStatement.lean`, 42 lines. `MovesLikeFortress M` says that the piece
  has the four moves of the Ferz and the four moves of the Dabbaba and that all its moves change
  x + y by an even number. It uses `Falafel.spiral` and `Straight.IsWalk`.
- **Theorems** (`Fortress/Theorems.lean`), for every such `M`: `deterministic`,
  `never_trapped`, `walks_odd_numbers` (term number n, counted from 0, is 2n + 1).
- **Instances:** `fortress_never_trapped`, `alfilerzbaba_never_trapped`, and
  `alfilerzbaba_eq_fortress` (the two make the same walk).
- **How the proof goes** (`Fortress/Main.lean`): the walk is every second square of the spiral,
  `Straight.w (2 * n)`. Two steps along the spiral are a Ferz move or a Dabbaba move
  (`step2_mem`). A move that keeps the parity of x + y leads from an odd number to an odd number
  (`Falafel.spiral_parity`), so no reachable square with a lower number is unvisited.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## The trapped pieces: Knight, Priest, Kangaroo, Carpenter, Leopard (25 Nov 2026)

Two more libraries in the same Lake project: `TrapCheck` (a program, compiled) and `Trap` (the
proofs). Build with `lake build Trap`: 9 min 39 s wall and 15 GB of memory at the peak on
25 Nov 2026, with three other jobs running (Kangaroo 529 s, Carpenter and Leopard 295 s).

- **Statement:** `TrapStatement.lean`, 108 lines. `IsRun M L a` asks the conditions of
  `Straight.IsWalk` of the first `L` moves only. `TrappedAfter M L t`: there is a run of `L`
  moves that ends on square `t`, and every square one move away from it was visited. The walk
  then has `L + 1` terms. `BeginsWith M l`: every run begins with the numbers of `l`.
- **General theorems** (`Trap/Main.lean`, no computation): `runs_agree`, `trap_is_the_end` (a
  trapped piece has no longer run and no `IsWalk`).
- **Per piece** (`Trap/Theorems.lean`, `Trap/Kangaroo.lean`, `Trap/Big.lean`): `knight_trapped`
  (2015 moves, square 2084), `priest_trapped` (1050, 858), `kangaroo_trapped` (59,676, 57,552),
  `carpenter_trapped` (253,925,075, 259,115,490), `leopard_trapped` (256,730,881, 267,545,105),
  and `knight_begins` to `leopard_begins`: the walk begins with the DATA line of the OEIS entry.
- **How the proof goes.** `TrapCheck/Check.lean` is the walk as a program, over a
  store of visited squares. `Trap/Machine.lean` proves `check_sound`: if `check S ms L t` is
  true for a lawful store, then `TrappedAfter {d | d ∈ ms} L t`. Two stores are proved lawful: the
  bits of one number (for the kernel) and an array (for compiled code).
- **Knight, Priest, Kangaroo, and all five `_begins`:** the kernel runs the program
  (`decide +kernel`). Axioms: `propext`, `Classical.choice`, `Quot.sound`. The Kangaroo is cut
  into 12 pieces of 5000 moves, since the kernel needs about 2 GB per 1000 moves;
  `Trap/KangarooData.lean` holds the generated states between the pieces, and the kernel checks
  each piece against them.
- **Carpenter, Leopard:** `native_decide` runs the compiled program. `#print axioms` shows one
  extra axiom for each (`..._check._native.native_decide.ax_1_1`): the Lean compiler is trusted
  for the run. `native_decide` uses compiled code only when built by `lake build`.
- No `sorry`.


## Without Mathlib (28 Nov 2026)

Until 28 Nov 2026 the project imported Mathlib (7.9 GB prebuilt). It now needs only Lean.

- **`Basic.lean`** (new, 46 lines) defines the few notions that came from Mathlib, each in one
  line. A reader of a statement file reads these definitions as well, instead of trusting
  Mathlib's.
- **Statement files.** The claims are unchanged, word for word. `Statement.lean` imports
  `Basic` instead of `Mathlib`; the comments that listed "notions taken from Mathlib" now say
  where each notion comes from. `LeaperStatement.lean` and `TrapStatement.lean` did not change.
- **Axioms.** The same as with Mathlib, theorem for theorem.
- **Proofs.** About 280 lines changed. The large case analyses (`Falafel/Greedy`, `Step`, `Laps`,
  `Leaper/Greedy`, the Trap machine) needed no change: they use `omega`, `decide` and `split`,
  which are part of Lean. `ring`, `linarith`, `norm_num` became `grind` or `omega`; each
  `nlinarith` became one explicit product `Int.mul_nonneg ...` followed by `grind`; `Nat.find`
  became a short descent; function iteration became a recursive definition; the order of the
  stamps (`StrictMono`, `toLex`) became a direct induction. The helpers are in
  `Falafel/Tactic.lean` (about 90 lines).
