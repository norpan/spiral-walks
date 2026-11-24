import StraightStatement

/-!
# The Fortress and the Alfilerzbaba walk 1, 3, 5, ...: the statement

A piece is given by its set `M` of moves, as changes of (x, y). This file is about every piece
that has the moves of the Ferz, (±1, ±1), and of the Dabbaba, (±2, 0) and (0, ±2), and whose
moves all change x + y by an even number.

- The Fortress has exactly these eight moves.
- The Alfilerzbaba also has the moves of the Alfil, (±2, ±2).

The square spiral is `Falafel.spiral` of `Statement.lean`, and a walk is `Straight.IsWalk` of
`StraightStatement.lean`. The proofs are in the folder `Fortress`; `Fortress/Theorems.lean` has
the theorems.

Notion taken from Mathlib, beyond those of the two files above: `Even k` (k = r + r for some r).
-/
namespace Fortress

open Falafel (spiral)
open Straight (IsWalk)

/-- The piece has the four moves of the Ferz and the four moves of the Dabbaba, and every move of
it changes x + y by an even number. -/
def MovesLikeFortress (M : Set (ℤ × ℤ)) : Prop :=
  (1, 1) ∈ M ∧ (1, -1) ∈ M ∧ (-1, 1) ∈ M ∧ (-1, -1) ∈ M ∧
  (2, 0) ∈ M ∧ (-2, 0) ∈ M ∧ (0, 2) ∈ M ∧ (0, -2) ∈ M ∧ ∀ d ∈ M, Even (d.1 + d.2)

/-- The rule decides every step: there is at most one infinite run. -/
def Deterministic : Prop :=
  ∀ M, MovesLikeFortress M → ∀ a b : ℕ → ℤ × ℤ, IsWalk M a → IsWalk M b → a = b

/-- The walk is never trapped: it has an infinite run. -/
def NeverTrapped : Prop :=
  ∀ M, MovesLikeFortress M → ∃ a : ℕ → ℤ × ℤ, IsWalk M a

/-- The walk is 1, 3, 5, ... (OEIS A005408): term number n, counted from 0, is 2n + 1. -/
def WalksOddNumbers : Prop :=
  ∀ M, MovesLikeFortress M → ∀ a : ℕ → ℤ × ℤ, IsWalk M a → ∀ n : ℕ, spiral (a n) = 2 * n + 1

end Fortress
