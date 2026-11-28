import Statement

/-!
# The terms of A399160 in closed form: the statement

`Statement.lean` says that the walk exists and which squares it visits. This file gives the
number of the square at every step from step 80 on, as a formula. It states Corollary 9 of the
paper. A reader who only wants the four claims of `Statement.lean` does not need it.

From step 80 on the walk runs in laps R = 4, 5, 6, ... around the origin. A step of lap R has an
index j, counted so that the lap's first staircase starts at index 0; the row before it has
negative indices. Every term is the square of an odd number plus a remainder.

Notions from Lean itself, beyond those of `Statement.lean`: `x / y` and `x % y` on `ℤ`
(quotient rounded down and remainder, for y > 0), and `(n : ℤ)` for a natural number n.
-/
namespace Falafel

/-- The step at which lap R ≥ 4 starts: (27 R² - 22 R - 24)/4 for even R and
(27 R² - 22 R - 33)/4 for odd R. -/
def start (R : ℤ) : ℤ := (27 * R ^ 2 - 22 * R - 24 - 9 * (R % 2)) / 4

/-- Lap 4 starts at step 80, lap 5 at step 133 and lap 6 at step 204. -/
example : start 4 = 80 ∧ start 5 = 133 ∧ start 6 = 204 := by decide

/-- The index of the first step of lap R: -R - 1 for even R and -R - 3 for odd R. -/
def first (R : ℤ) : ℤ := -(R + 1 + 2 * (R % 2))

/-- The term at place t of the last part of lap R, the way back. -/
def backTerm (R t : ℤ) : ℤ :=
  if R % 2 = 0 then
    if t % 3 = 0 then (4 * R - 4 * (t / 3) - 1) ^ 2 + (3 * R - 6 * (t / 3) - 4)
    else if t % 3 = 1 then (4 * R - 4 * (t / 3) - 3) ^ 2 + (3 * R - 6 * (t / 3) - 6)
    else (4 * R - 4 * (t / 3) - 1) ^ 2 + (3 * R - 6 * (t / 3) - 6)
  else if t % 3 = 0 then (4 * R - 4 * (t / 3) - 3) ^ 2 + (3 * R - 6 * (t / 3) - 5)
  else if t % 3 = 1 then (4 * R - 4 * (t / 3) - 1) ^ 2 + (3 * R - 6 * (t / 3) - 5)
  else (4 * R - 4 * (t / 3) - 3) ^ 2 + (3 * R - 6 * (t / 3) - 7)

/-- The term at index j of lap R ≥ 4. -/
def term (R j : ℤ) : ℤ :=
  if j < 0 then                         -- the row
    if R % 2 = 0 then
      if j = -R - 1 then (2 * R - 1) ^ 2 + (8 * R)
      else if j = -R then (2 * R + 1) ^ 2 + 2
      else (4 * R + 2 * j - 1) ^ 2 + (14 * R + 6 * j)
    else if j = -R - 3 then (2 * R + 3) ^ 2 + 6
    else if j = -R - 2 then (2 * R + 5) ^ 2 + 6
    else if j = -R - 1 then (2 * R + 1) ^ 2 + 2
    else (4 * R + 2 * j - 1) ^ 2 + (14 * R + 6 * j)
  else if j < 2 * R - 4 then            -- first staircase
    if j % 2 = 0 then (4 * R - 5) ^ 2 + (14 * R - j - 14)
    else (4 * R - 3) ^ 2 + (14 * R - j - 7)
  else if j < 2 * R + 2 then            -- first corner
    if j = 2 * R - 4 then (4 * R - 7) ^ 2 + (12 * R - 18)
    else if j = 2 * R - 3 then (4 * R - 5) ^ 2 + (12 * R - 14)
    else if j = 2 * R - 2 then (4 * R - 5) ^ 2 + (12 * R - 10)
    else if j = 2 * R - 1 then (4 * R - 3) ^ 2 + (12 * R - 4)
    else if j = 2 * R then (4 * R - 5) ^ 2 + (12 * R - 12)
    else (4 * R - 3) ^ 2 + (12 * R - 8)
  else if j < 6 * R - 5 then            -- second staircase
    if j % 2 = 0 then (4 * R - 1) ^ 2 + (14 * R - j - 2)
    else (4 * R - 3) ^ 2 + (14 * R - j - 7)
  else if j < 6 * R + 1 then            -- second corner
    if j = 6 * R - 5 then (4 * R - 5) ^ 2 + (8 * R - 8)
    else if j = 6 * R - 4 then (4 * R - 3) ^ 2 + (8 * R - 6)
    else if j = 6 * R - 3 then (4 * R - 3) ^ 2 + (8 * R - 2)
    else if j = 6 * R - 2 then (4 * R - 1) ^ 2 + (8 * R + 2)
    else if j = 6 * R - 1 then (4 * R - 3) ^ 2 + (8 * R - 4)
    else (4 * R - 1) ^ 2 + (8 * R - 2)
  else if j < 10 * R - 4 then           -- third staircase
    if j % 2 = 1 then (4 * R + 1) ^ 2 + (14 * R - j + 1)
    else (4 * R - 1) ^ 2 + (14 * R - j - 2)
  else if j < 10 * R + 2 then           -- third corner
    if j = 10 * R - 4 then (4 * R - 3) ^ 2 + (4 * R - 2)
    else if j = 10 * R - 3 then (4 * R - 1) ^ 2 + (4 * R - 2)
    else if j = 10 * R - 2 then (4 * R - 1) ^ 2 + (4 * R + 2)
    else if j = 10 * R - 1 then (4 * R + 1) ^ 2 + (4 * R + 4)
    else if j = 10 * R then (4 * R - 1) ^ 2 + (4 * R)
    else (4 * R + 1) ^ 2 + (4 * R)
  else if j < 11 * R + 3 then           -- fourth staircase
    if j % 2 = 0 then (4 * R + 3) ^ 2 + (14 * R - j + 2)
    else (4 * R + 1) ^ 2 + (14 * R - j + 1)
  else backTerm R (j - (11 * R + 3))    -- the way back

/-- Corollary 9. If lap R ≥ 4 has started at step n and lap R + 1 has not, then the number of
the square at step n is `term R j` with j = first R + (n - start R). This number is
A399160(n + 1). -/
def TermFormula : Prop :=
  ∀ a : ℕ → ℤ × ℤ, IsWalk a → ∀ R : ℤ, 4 ≤ R → ∀ n : ℕ, start R ≤ n → n < start (R + 1) →
    spiral (a n) = term R (first R + (n - start R))

end Falafel
