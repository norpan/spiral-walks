import Statement
import Falafel.Numbers
import Falafel.Tactic

/-!
# Comparing spiral numbers

The spiral number of (x, y) is (2 rg - 1)² + ps, with the ring `rg` and the position `ps`
written with `if` only. So comparing spiral numbers is comparing (rg, ps) pairs, which `omega`
can do.
-/
namespace Leaper

open Falafel (spiral)

/-- The ring max(|x|, |y|). -/
def rg (x y : ℤ) : ℤ :=
  if (if 0 ≤ y then y else -y) ≤ (if 0 ≤ x then x else -x) then (if 0 ≤ x then x else -x)
  else (if 0 ≤ y then y else -y)

/-- The position within the ring: 1 to 8 rg, and 0 for the origin. -/
def ps (x y : ℤ) : ℤ :=
  if x = rg x y ∧ y > -rg x y then y + rg x y
  else if y = rg x y then 3 * rg x y - x
  else if x = -rg x y then 5 * rg x y - y
  else 7 * rg x y + x

theorem max_eq_rg (x y : ℤ) : max |x| |y| = rg x y :=
  (Falafel.ring_iff x y _).mpr (by unfold rg; split_omega)

theorem spiral_key (x y : ℤ) : spiral (x, y) = (2 * rg x y - 1) ^ 2 + ps x y := by
  rw [Falafel.spiral_eq x y _ (max_eq_rg x y)]
  unfold ps
  split <;> grind

/-- Ring r ends before ring s begins, for r < s. -/
theorem ring_step (r s : ℤ) (h0 : 0 ≤ r) (h : r < s) :
    (2 * r - 1) ^ 2 + 8 * r ≤ (2 * s - 1) ^ 2 := by
  have := Int.mul_nonneg (show (0 : ℤ) ≤ s - r - 1 by omega) (show (0 : ℤ) ≤ s + r by omega)
  grind

theorem rg_nonneg (x y : ℤ) : 0 ≤ rg x y := by
  unfold rg
  split_omega

theorem ps_bounds (x y : ℤ) :
    0 ≤ ps x y ∧ ps x y ≤ 8 * rg x y ∧ (1 ≤ rg x y → 1 ≤ ps x y) := by
  unfold ps rg
  split_omega

/-- Ring and position determine the square. -/
theorem key_inj (x y x' y' : ℤ) :
    rg x y = rg x' y' → ps x y = ps x' y' → x = x' ∧ y = y' := by
  intro hr hp
  have b := (Falafel.ring_iff x y _).mp (max_eq_rg x y)
  have b' := (Falafel.ring_iff x' y' _).mp (max_eq_rg x' y')
  unfold ps at hp
  rw [← hr] at hp b'
  generalize rg x y = r at hp b b'
  split at hp <;> omega

/-- Comparing (rg, ps) compares spiral numbers. -/
theorem spiral_le_of_key (x y x' y' : ℤ)
    (h : rg x y < rg x' y' ∨ (rg x y = rg x' y' ∧ ps x y ≤ ps x' y')) :
    spiral (x, y) ≤ spiral (x', y') := by
  rw [spiral_key, spiral_key]
  have h1 := ps_bounds x y
  have h2 := ps_bounds x' y'
  rcases h with h | ⟨h, h'⟩
  · have h4 := ring_step _ _ (rg_nonneg x y) h
    omega
  · rw [h]
    omega

/-- Different squares have different spiral numbers. -/
theorem spiral_inj (x y x' y' : ℤ) (h : spiral (x, y) = spiral (x', y')) : x = x' ∧ y = y' := by
  rw [spiral_key, spiral_key] at h
  have h1 := ps_bounds x y
  have h2 := ps_bounds x' y'
  have hr : rg x y = rg x' y' := by
    rcases Int.lt_trichotomy (rg x y) (rg x' y') with hlt | heq | hgt
    · have h4 := ring_step _ _ (rg_nonneg x y) hlt
      have h5 := h2.2.2 (by have := rg_nonneg x y; omega)
      omega
    · exact heq
    · have h4 := ring_step _ _ (rg_nonneg x' y') hgt
      have h5 := h1.2.2 (by have := rg_nonneg x' y'; omega)
      omega
  rw [hr] at h
  exact key_inj x y x' y' hr (by omega)

end Leaper
