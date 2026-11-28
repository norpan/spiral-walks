import Leaper.Spiral

/-!
# The diamond path of the (1, 1)-leaper

Squares (p, q) with p + q even. `dd` is |p| + |q|, twice the number of the diamond. `idx` is the
place on the diamond, clockwise from (1, dd - 1). `nx`, `ny` give the next square. `rk` is the
number of steps the walk needs to reach the square.
-/
namespace Leaper

open Falafel (spiral)

/-- |p| + |q|. -/
def dd (p q : ℤ) : ℤ := (if 0 ≤ p then p else -p) + (if 0 ≤ q then q else -q)

/-- The place on the diamond: 0 at (1, dd - 1), then clockwise up to 4 dd - 1 at (0, dd).
For the origin it is -1. -/
def idx (p q : ℤ) : ℤ :=
  if 1 ≤ p ∧ 0 ≤ q then p - 1
  else if 0 ≤ p ∧ q < 0 then dd p q - 1 - q
  else if p < 0 ∧ q ≤ 0 then 2 * dd p q - 1 - p
  else 3 * dd p q - 1 + q

/-- The next square, first coordinate. -/
def nx (p q : ℤ) : ℤ :=
  if 1 ≤ p ∧ 1 ≤ q then p + 1 else if 1 ≤ p then p - 1 else if q ≤ -1 then p - 1 else p + 1

/-- The next square, second coordinate. -/
def ny (p q : ℤ) : ℤ :=
  if 1 ≤ p ∧ 1 ≤ q then q - 1 else if 1 ≤ p then q - 1 else if q ≤ -1 then q + 1 else q + 1

/-- The step at which the walk stands on the square: 0 for the origin, and
dd (dd - 2) + 1 + idx on a diamond. -/
def rk (p q : ℤ) : ℤ := dd p q * (dd p q - 2) + 1 + idx p q

/-- (p, q) comes before (p', q') on the path. -/
def Before (p q p' q' : ℤ) : Prop :=
  dd p q < dd p' q' ∨ (dd p q = dd p' q' ∧ idx p q < idx p' q')

theorem par_next (p q : ℤ) (h : (p + q) % 2 = 0) : (nx p q + ny p q) % 2 = 0 := by
  unfold nx ny
  split_omega

/-- The next square is one diagonal step away. -/
theorem next_diag (p q : ℤ) :
    (nx p q = p + 1 ∨ nx p q = p - 1) ∧ (ny p q = q + 1 ∨ ny p q = q - 1) := by
  unfold nx ny
  split_omega

theorem bounds (p q : ℤ) (h : (p + q) % 2 = 0) :
    0 ≤ dd p q ∧ dd p q % 2 = 0 ∧ -1 ≤ idx p q ∧ idx p q ≤ 4 * dd p q - 1 ∧
      (1 ≤ dd p q → 0 ≤ idx p q) := by
  unfold idx dd
  split_omega

/-- The next square is the next place on the diamond, or the first place of the next diamond. -/
theorem next_class (p q : ℤ) (h : (p + q) % 2 = 0) :
    (dd (nx p q) (ny p q) = dd p q ∧ idx (nx p q) (ny p q) = idx p q + 1) ∨
      (dd (nx p q) (ny p q) = dd p q + 2 ∧ idx (nx p q) (ny p q) = 0 ∧
        idx p q = 4 * dd p q - 1) := by
  unfold idx dd nx ny
  split_omega

theorem rk_next (p q : ℤ) (h : (p + q) % 2 = 0) : rk (nx p q) (ny p q) = rk p q + 1 := by
  unfold rk
  rcases next_class p q h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2]; grind
  · rw [h1, h2, h3]; grind

theorem rk_nonneg (p q : ℤ) (h : (p + q) % 2 = 0) : 0 ≤ rk p q := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bounds p q h
  unfold rk
  rcases (show 0 = dd p q ∨ 0 < dd p q by omega) with h5 | h5
  · rw [← h5]; omega
  · have : 2 ≤ dd p q := by omega
    have := h4 (by omega)
    have := Int.mul_nonneg (show 0 ≤ dd p q by omega) (show 0 ≤ dd p q - 2 by omega)
    grind

theorem rk_lt_of_before (p q p' q' : ℤ) (h : (p + q) % 2 = 0) (h' : (p' + q') % 2 = 0)
    (hb : Before p q p' q') : rk p q < rk p' q' := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bounds p q h
  obtain ⟨h0', h1', h2', h3', h4'⟩ := bounds p' q' h'
  unfold rk
  rcases hb with hb | ⟨hb, hb'⟩
  · have e : dd p q + 2 ≤ dd p' q' := by omega
    have := h4' (by omega)
    have := Int.mul_nonneg (show (0 : ℤ) ≤ dd p' q' - (dd p q + 2) by omega)
      (show (0 : ℤ) ≤ dd p' q' + dd p q by omega)
    grind
  · rw [hb]; omega

/-- Diamond and place determine the square. -/
theorem pt_inj (p q p' q' : ℤ) : dd p q = dd p' q' → idx p q = idx p' q' → p = p' ∧ q = q' := by
  unfold idx dd
  split_omega

theorem rk_inj (p q p' q' : ℤ) (h : (p + q) % 2 = 0) (h' : (p' + q') % 2 = 0)
    (e : rk p q = rk p' q') : p = p' ∧ q = q' := by
  by_cases b1 : Before p q p' q'
  · have := rk_lt_of_before p q p' q' h h' b1; omega
  by_cases b2 : Before p' q' p q
  · have := rk_lt_of_before p' q' p q h' h b2; omega
  unfold Before at b1 b2
  exact pt_inj p q p' q' (by omega) (by omega)

end Leaper
