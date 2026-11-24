import Statement

/-!
# Pieces that can move straight never get trapped: the statement

A piece is given by its set `M` of moves, as changes of (x, y). This file is about every piece
that can move s squares straight in each of the four directions and whose moves all change both
coordinates by multiples of s, for some s > 0.

- s = 1: the Wazir, with the moves (±1, 0) and (0, ±1), and every piece that has the Wazir's
  moves. For s = 1 the condition on the other moves is empty.
- s = 2: the Dabbaba, with the moves (±2, 0) and (0, ±2) (OEIS A399158), and the Alibaba, which
  also has (±2, ±2).

The square spiral is `Falafel.spiral` of `Statement.lean`. The proofs are in the folder
`Straight`; `Straight/Theorems.lean` has the theorems.

Notions taken from Mathlib, beyond those of `Statement.lean`: `Set` and `∈`, `s ∣ x` (x is a
multiple of s) and `StrictMono f` (`f m < f n` whenever `m < n`).
-/
namespace Straight

open Falafel (spiral)

/-- `a 0, a 1, a 2, ...` is an infinite run of the walk of the piece with the moves `M`. It
starts on square 1 and visits no square twice. Each next square is one move away. Every square
one move away with a lower number than the next square was visited before. -/
structure IsWalk (M : Set (ℤ × ℤ)) (a : ℕ → ℤ × ℤ) : Prop where
  start : a 0 = (0, 0)
  injective : Function.Injective a
  move : ∀ n, a (n + 1) - a n ∈ M
  lowest : ∀ n q, q - a n ∈ M → spiral q < spiral (a (n + 1)) → ∃ m ≤ n, a m = q

/-- The piece can move s squares straight in each of the four directions, and every move of it
changes both coordinates by a multiple of s. -/
def MovesStraight (s : ℤ) (M : Set (ℤ × ℤ)) : Prop :=
  (s, 0) ∈ M ∧ (-s, 0) ∈ M ∧ (0, s) ∈ M ∧ (0, -s) ∈ M ∧ ∀ d ∈ M, s ∣ d.1 ∧ s ∣ d.2

/-- The rule decides every step: there is at most one infinite run. -/
def Deterministic : Prop :=
  ∀ s : ℤ, 0 < s → ∀ M, MovesStraight s M → ∀ a b : ℕ → ℤ × ℤ, IsWalk M a → IsWalk M b → a = b

/-- The walk is never trapped: it has an infinite run. -/
def NeverTrapped : Prop :=
  ∀ s : ℤ, 0 < s → ∀ M, MovesStraight s M → ∃ a : ℕ → ℤ × ℤ, IsWalk M a

/-- The walk visits exactly the squares with both coordinates multiples of s, and it visits them
in the order of their numbers: the sequence is increasing. -/
def VisitsLatticeInOrder : Prop :=
  ∀ s : ℤ, 0 < s → ∀ M, MovesStraight s M → ∀ a : ℕ → ℤ × ℤ, IsWalk M a →
    (∀ x y : ℤ, (∃ n, a n = (x, y)) ↔ s ∣ x ∧ s ∣ y) ∧ StrictMono (fun n => spiral (a n))

/-- A piece that has the Wazir's moves walks 1, 2, 3, ...: its n-th term is n (OEIS A000027). -/
def WazirWalksInOrder : Prop :=
  ∀ M, MovesStraight 1 M → ∀ a : ℕ → ℤ × ℤ, IsWalk M a → ∀ n : ℕ, spiral (a n) = n + 1

end Straight
