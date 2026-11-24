import Statement

/-!
# The Ferz walk (OEIS A316884) and the Alfil walk (OEIS A317467) never end: the statement

The (s, s)-leaper moves s squares diagonally. The Ferz is s = 1 and the Alfil is s = 2. This file
defines the moves and the walk and states four claims. The first three are for every
leap length s > 0, the fourth is for the Ferz. The square spiral is `Falafel.spiral` of
`Statement.lean`. The proofs are in the folder `Leaper`; `Leaper/Theorems.lean` has the theorems.
-/
namespace Leaper

open Falafel (spiral)

/-- The (s, s)-leaper moves from (x, y) to (x ± s, y ± s). -/
def IsMove (s : ℤ) (p q : ℤ × ℤ) : Prop :=
  |q.1 - p.1| = s ∧ |q.2 - p.2| = s

/-- `a 0, a 1, a 2, ...` is an infinite run of the walk of the (s, s)-leaper. It starts on
square 1 and visits no square twice. Each next square is one move away. Every square one move
away with a lower number than the next square was visited before. -/
structure IsWalk (s : ℤ) (a : ℕ → ℤ × ℤ) : Prop where
  start : a 0 = (0, 0)
  injective : Function.Injective a
  move : ∀ n, IsMove s (a n) (a (n + 1))
  lowest : ∀ n q, IsMove s (a n) q → spiral q < spiral (a (n + 1)) → ∃ m ≤ n, a m = q

/-- For every leap length s > 0 the rule decides every step: there is at most one infinite
run. -/
def Deterministic : Prop :=
  ∀ s : ℤ, 0 < s → ∀ a b : ℕ → ℤ × ℤ, IsWalk s a → IsWalk s b → a = b

/-- For every leap length s > 0 the walk is never trapped: it has an infinite run. The n-th
term of the sequence is `spiral (a (n - 1))`. -/
def NeverTrapped : Prop := ∀ s : ℤ, 0 < s → ∃ a : ℕ → ℤ × ℤ, IsWalk s a

/-- For every leap length s > 0 the walk visits every square (s i, s j) with i + j even, and no
other square. -/
def VisitsExactlyReachableSquares : Prop :=
  ∀ s : ℤ, 0 < s → ∀ a : ℕ → ℤ × ℤ, IsWalk s a →
    ∀ x y : ℤ, (∃ n, a n = (x, y)) ↔ ∃ i j : ℤ, Even (i + j) ∧ x = s * i ∧ y = s * j

/-- For the Ferz (s = 1): every term is an odd positive integer, and every odd positive integer
is a term exactly once. So A316884 is a permutation of the odd positive integers. -/
def FerzPermutationOfOddNumbers : Prop :=
  ∀ a : ℕ → ℤ × ℤ, IsWalk 1 a →
    (∀ n, 0 < spiral (a n) ∧ Odd (spiral (a n))) ∧
    (∀ k : ℤ, 0 < k → Odd k → ∃! n, spiral (a n) = k)

end Leaper
