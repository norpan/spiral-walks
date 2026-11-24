import Statement
import Falafel.Stamp
import Falafel.Tactic

/-!
# Spiral numbers in (u, v) coordinates

The spiral number of the square (x, y) = (u + v, u - v) is (2 ring - 1)² + rpos. So comparing
spiral numbers is comparing (ring, rpos) pairs.
-/
namespace Falafel

/-- Ring r ends before ring s begins, for r < s. The only non-linear fact in the proof. -/
theorem ring_step (r s : ℤ) (h0 : 0 ≤ r) (h : r < s) :
    (2 * r - 1) ^ 2 + 8 * r ≤ (2 * s - 1) ^ 2 := by
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ s - r - 1 by omega) (show (0 : ℤ) ≤ s + r by omega)]

theorem ring_eq_abs (u v : ℤ) : ring u v = |u| + |v| := by
  unfold ring
  rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases v with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2] <;> split_ifs <;> omega

theorem ring_nonneg (u v : ℤ) : 0 ≤ ring u v := by
  rw [ring_eq_abs]
  positivity

theorem rpos_bounds (u v : ℤ) :
    0 ≤ rpos u v ∧ rpos u v ≤ 8 * ring u v ∧ (1 ≤ ring u v → 1 ≤ rpos u v) := by
  unfold ring rpos
  split_ifs <;> omega

/-- Ring and position determine the square. -/
theorem key_inj (a b c d : ℤ) : ring a b = ring c d → rpos a b = rpos c d → a = c ∧ b = d := by
  unfold ring rpos
  split_omega

/-- The ring max(|x|, |y|) of the statement is `ring`. -/
theorem max_abs_eq_ring (u v : ℤ) : max |u + v| |u - v| = ring u v := by
  unfold ring
  rcases abs_cases (u + v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (u - v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2, max_def] <;> split_ifs <;> omega

/-- The spiral number in terms of ring and position. -/
theorem spiral_uv (u v : ℤ) :
    spiral (u + v, u - v) = (2 * ring u v - 1) ^ 2 + rpos u v := by
  have hr : ring u v = (if u ≥ 0 then u else -u) + (if v ≥ 0 then v else -v) := rfl
  simp only [spiral, max_abs_eq_ring]
  unfold rpos
  generalize ring u v = r at hr ⊢
  generalize (2 * r - 1) ^ 2 = N
  split_ifs at hr ⊢ <;> omega

/-- Comparing (ring, rpos) compares spiral numbers. -/
theorem spiral_le_of_keyLE (a b c d : ℤ) (h : KeyLE c d a b) :
    spiral (c + d, c - d) ≤ spiral (a + b, a - b) := by
  rw [spiral_uv, spiral_uv]
  have h1 := rpos_bounds a b
  have h2 := rpos_bounds c d
  rcases h with h | ⟨h, h'⟩
  · have h4 := ring_step (ring c d) (ring a b) (ring_nonneg c d) h
    linarith
  · rw [h]
    linarith

/-- Squares of the Falafel's colour with equal spiral numbers are equal. -/
theorem spiral_uv_inj (a b c d : ℤ) (h : spiral (a + b, a - b) = spiral (c + d, c - d)) :
    a = c ∧ b = d := by
  rw [spiral_uv, spiral_uv] at h
  have h1 := rpos_bounds a b
  have h2 := rpos_bounds c d
  have hr : ring a b = ring c d := by
    rcases lt_trichotomy (ring a b) (ring c d) with hlt | heq | hgt
    · have h4 := ring_step _ _ (ring_nonneg a b) hlt
      have h5 := h2.2.2 (by linarith [ring_nonneg a b])
      linarith
    · exact heq
    · have h4 := ring_step _ _ (ring_nonneg c d) hgt
      have h5 := h1.2.2 (by linarith [ring_nonneg c d])
      linarith
  rw [hr] at h
  exact key_inj a b c d hr (by linarith)

end Falafel
