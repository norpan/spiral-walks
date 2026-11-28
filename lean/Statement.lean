import Basic

/-!
# The Falafel walk (OEIS A399160) never ends: the statement

This file is the only part a reader has to trust. It defines the square spiral, the Falafel's
moves and the walk, and states four claims. Each claim is one statement of the paper and is named
after it in its comment. The proofs are in the other files; `Falafel/Theorems.lean` has the four
theorems.

Notions from Lean itself: `max`, `x ^ 2`, `Function.Injective a` (`a m = a n` only if `m = n`).
Notions defined in `Basic.lean` (one line each): `ℕ`, `ℤ`, `|x|` (absolute value),
`Even n` (`n = k + k` for some `k`), `Odd k` (`k = 2 * k' + 1` for some `k'`) and `∃! n, P n`
(exactly one `n` has `P n`). The project does not use Mathlib.
-/
namespace Falafel

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

/-- The picture on the OEIS page: rows y = 2, 1, 0, -1, -2, each with x = -2, ..., 2. -/
example :
    [2, 1, 0, -1, -2].map (fun y : ℤ => [-2, -1, 0, 1, 2].map (fun x : ℤ => spiral (x, y)))
      = [[17, 16, 15, 14, 13],
         [18,  5,  4,  3, 12],
         [19,  6,  1,  2, 11],
         [20,  7,  8,  9, 10],
         [21, 22, 23, 24, 25]] := by
  decide

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

end Falafel
