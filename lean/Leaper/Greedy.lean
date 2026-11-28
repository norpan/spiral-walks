import Leaper.Model

/-!
# The next square has the lowest number

From a square P of the path, a diagonal neighbour that does not come before P on the path has
no lower spiral number than the next square, for every leap length s.

The proof has two halves. `class_pp` to `class_mp` list, for each of the four diagonal
directions, where P can be if the neighbour does not come before it. `k0pm` to `k9` compare
the spiral numbers in each of those places. There the squares are scaled by s, and the products
s p and s q are plain integers A and B with the sign facts `sc_*`.
-/
namespace Leaper

open Falafel (spiral)

/-! ## Scaling -/

theorem sc_zero (s z : ℤ) (h : z = 0) : s * z = 0 := by rw [h]; grind
theorem sc_one (s z : ℤ) (h : z = 1) : s * z = s := by rw [h]; grind
theorem sc_ge (s z : ℤ) (hs : 0 < s) (h : 1 ≤ z) : s ≤ s * z := by
  have := Int.mul_nonneg (Int.le_of_lt hs) (show 0 ≤ z - 1 by omega); grind
theorem sc_le (s z : ℤ) (hs : 0 < s) (h : z ≤ -1) : s * z ≤ -s := by
  have := Int.mul_nonneg (Int.le_of_lt hs) (show 0 ≤ -z - 1 by omega); grind
theorem sc_nonneg (s z : ℤ) (hs : 0 < s) (h : 0 ≤ z) : 0 ≤ s * z :=
  Int.mul_nonneg (Int.le_of_lt hs) h
theorem sc_nonpos (s z : ℤ) (hs : 0 < s) (h : z ≤ 0) : s * z ≤ 0 := by
  have := Int.mul_nonneg (Int.le_of_lt hs) (show 0 ≤ -z by omega); grind

/-! ## Comparing two squares -/

/-- (x, y) has no higher spiral number than (x', y'), as a comparison of ring and position. -/
def Key (x y x' y' : ℤ) : Prop :=
  rg x y < rg x' y' ∨ (rg x y = rg x' y' ∧ ps x y ≤ ps x' y')

theorem ps_spec (x y : ℤ) :
    (x = rg x y → y > -rg x y → ps x y = y + rg x y) ∧
      (¬ (x = rg x y ∧ y > -rg x y) → y = rg x y → ps x y = 3 * rg x y - x) ∧
      (¬ (x = rg x y ∧ y > -rg x y) → y ≠ rg x y → x = -rg x y → ps x y = 5 * rg x y - y) ∧
      (¬ (x = rg x y ∧ y > -rg x y) → y ≠ rg x y → x ≠ -rg x y → ps x y = 7 * rg x y + x) := by
  unfold ps
  generalize rg x y = r
  split_omega

/-- To compare two squares it is enough to know, for each, that it lies on the border of the
box of its ring, and its position on each of the four sides. -/
theorem key_of (x y x' y' : ℤ)
    (h : ∀ r r' P P' : ℤ,
      ((-r ≤ x ∧ x ≤ r) ∧ (-r ≤ y ∧ y ≤ r) ∧ (x = r ∨ x = -r ∨ y = r ∨ y = -r)) →
      ((-r' ≤ x' ∧ x' ≤ r') ∧ (-r' ≤ y' ∧ y' ≤ r') ∧ (x' = r' ∨ x' = -r' ∨ y' = r' ∨ y' = -r')) →
      ((x = r → y > -r → P = y + r) ∧ (¬ (x = r ∧ y > -r) → y = r → P = 3 * r - x) ∧
        (¬ (x = r ∧ y > -r) → y ≠ r → x = -r → P = 5 * r - y) ∧
        (¬ (x = r ∧ y > -r) → y ≠ r → x ≠ -r → P = 7 * r + x)) →
      ((x' = r' → y' > -r' → P' = y' + r') ∧ (¬ (x' = r' ∧ y' > -r') → y' = r' → P' = 3 * r' - x') ∧
        (¬ (x' = r' ∧ y' > -r') → y' ≠ r' → x' = -r' → P' = 5 * r' - y') ∧
        (¬ (x' = r' ∧ y' > -r') → y' ≠ r' → x' ≠ -r' → P' = 7 * r' + x')) →
      r < r' ∨ (r = r' ∧ P ≤ P')) :
    Key x y x' y' :=
  h _ _ _ _ ((Falafel.ring_iff _ _ _).mp (max_eq_rg x y))
    ((Falafel.ring_iff _ _ _).mp (max_eq_rg x' y')) (ps_spec x y) (ps_spec x' y')

/-- Closes a comparison of two explicit squares. -/
macro "key_omega" : tactic =>
  `(tactic| (refine key_of _ _ _ _ fun r r' P P' b b' c c' => ?_; omega))

/-- From the origin: (s, s) against (s, -s). -/
theorem k0pm (s A B : ℤ) (hs : 0 < s) (hA : A = 0) (hB : B = 0) :
    Key (A + s) (B + s) (A + s) (B - s) := by key_omega

/-- From the origin: (s, s) against (-s, -s). -/
theorem k0mm (s A B : ℤ) (hs : 0 < s) (hA : A = 0) (hB : B = 0) :
    Key (A + s) (B + s) (A - s) (B - s) := by key_omega

/-- x > 0, y > 0: next square against the outward square. -/
theorem k2 (s A B : ℤ) (hs : 0 < s) (hA : s ≤ A) (hB : s ≤ B) :
    Key (A + s) (B - s) (A + s) (B + s) := by key_omega

/-- The first square of a diamond: next square against the last square of the diamond. -/
theorem k3 (s A B : ℤ) (hs : 0 < s) (hA : A = s) (hB : s ≤ B) :
    Key (A + s) (B - s) (A - s) (B + s) := by key_omega

/-- x > 0, y ≤ 0: next square against the outward square. -/
theorem k4 (s A B : ℤ) (hs : 0 < s) (hA : s ≤ A) (hB : B ≤ 0) :
    Key (A - s) (B - s) (A + s) (B - s) := by key_omega

/-- On the positive x axis: next square against the other outward square. -/
theorem k5 (s A B : ℤ) (hs : 0 < s) (hA : s ≤ A) (hB : B = 0) :
    Key (A - s) (B - s) (A + s) (B + s) := by key_omega

/-- x ≤ 0, y < 0: next square against the outward square. -/
theorem k6 (s A B : ℤ) (hs : 0 < s) (hA : A ≤ 0) (hB : B ≤ -s) :
    Key (A - s) (B + s) (A - s) (B - s) := by key_omega

/-- On the negative y axis: next square against the other outward square. -/
theorem k7 (s A B : ℤ) (hs : 0 < s) (hA : A = 0) (hB : B ≤ -s) :
    Key (A - s) (B + s) (A + s) (B - s) := by key_omega

/-- x ≤ 0, y ≥ 0: next square against the outward square. -/
theorem k8 (s A B : ℤ) (hs : 0 < s) (hA : A ≤ 0) (hB : 0 ≤ B) :
    Key (A + s) (B + s) (A - s) (B + s) := by key_omega

/-- On the negative x axis: next square against the other outward square. -/
theorem k9 (s A B : ℤ) (hs : 0 < s) (hA : A ≤ -s) (hB : B = 0) :
    Key (A + s) (B + s) (A - s) (B - s) := by key_omega

/-! ## Where a neighbour does not come before -/

theorem class_pp (p q : ℤ) (hpar : (p + q) % 2 = 0) :
    ¬ Before (p + 1) (q + 1) p q → (1 ≤ p ∧ 1 ≤ q) ∨ (1 ≤ p ∧ q = 0) ∨ (p ≤ 0 ∧ 0 ≤ q) := by
  unfold Before idx dd
  split_omega

theorem class_pm (p q : ℤ) (hpar : (p + q) % 2 = 0) :
    ¬ Before (p + 1) (q - 1) p q →
      (p = 0 ∧ q = 0) ∨ (1 ≤ p ∧ 1 ≤ q) ∨ (1 ≤ p ∧ q ≤ 0) ∨ (p = 0 ∧ q ≤ -1) := by
  unfold Before idx dd
  split_omega

theorem class_mm (p q : ℤ) (hpar : (p + q) % 2 = 0) :
    ¬ Before (p - 1) (q - 1) p q →
      (p = 0 ∧ q = 0) ∨ (1 ≤ p ∧ q ≤ 0) ∨ (p ≤ 0 ∧ q ≤ -1) ∨ (p ≤ -1 ∧ q = 0) := by
  unfold Before idx dd
  split_omega

theorem class_mp (p q : ℤ) (hpar : (p + q) % 2 = 0) :
    ¬ Before (p - 1) (q + 1) p q → (p = 1 ∧ 1 ≤ q) ∨ (p ≤ 0 ∧ q ≤ -1) ∨ (p ≤ 0 ∧ 0 ≤ q) := by
  unfold Before idx dd
  split_omega

/-! ## Greedy, one direction at a time -/

theorem greedy_pp (s p q : ℤ) (hs : 0 < s) (hpar : (p + q) % 2 = 0)
    (h : ¬ Before (p + 1) (q + 1) p q) :
    spiral (s * nx p q, s * ny p q) ≤ spiral (s * (p + 1), s * (q + 1)) := by
  rcases class_pp p q hpar h with c | c | c
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k2 s _ _ hs (sc_ge s p hs c.1) (sc_ge s q hs c.2))
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k5 s _ _ hs (sc_ge s p hs c.1) (sc_zero s q c.2))
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]

theorem greedy_pm (s p q : ℤ) (hs : 0 < s) (hpar : (p + q) % 2 = 0)
    (h : ¬ Before (p + 1) (q - 1) p q) :
    spiral (s * nx p q, s * ny p q) ≤ spiral (s * (p + 1), s * (q - 1)) := by
  rcases class_pm p q hpar h with c | c | c | c
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k0pm s _ _ hs (sc_zero s p c.1) (sc_zero s q c.2))
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k4 s _ _ hs (sc_ge s p hs c.1) (sc_nonpos s q hs c.2))
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k7 s _ _ hs (sc_zero s p c.1) (sc_le s q hs c.2))

theorem greedy_mm (s p q : ℤ) (hs : 0 < s) (hpar : (p + q) % 2 = 0)
    (h : ¬ Before (p - 1) (q - 1) p q) :
    spiral (s * nx p q, s * ny p q) ≤ spiral (s * (p - 1), s * (q - 1)) := by
  rcases class_mm p q hpar h with c | c | c | c
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k0mm s _ _ hs (sc_zero s p c.1) (sc_zero s q c.2))
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k6 s _ _ hs (sc_nonpos s p hs c.1) (sc_le s q hs c.2))
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k9 s _ _ hs (sc_le s p hs c.1) (sc_zero s q c.2))

theorem greedy_mp (s p q : ℤ) (hs : 0 < s) (hpar : (p + q) % 2 = 0)
    (h : ¬ Before (p - 1) (q + 1) p q) :
    spiral (s * nx p q, s * ny p q) ≤ spiral (s * (p - 1), s * (q + 1)) := by
  rcases class_mp p q hpar h with c | c | c
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q - 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k3 s _ _ hs (sc_one s p c.1) (sc_ge s q hs c.2))
  · have hx : nx p q = p - 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]
  · have hx : nx p q = p + 1 := by unfold nx; split_omega
    have hy : ny p q = q + 1 := by unfold ny; split_omega
    rw [hx, hy]; simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
    exact spiral_le_of_key _ _ _ _ (k8 s _ _ hs (sc_nonpos s p hs c.1) (sc_nonneg s q hs c.2))

/-- **Greedy.** A diagonal neighbour of (p, q) that does not come before it on the path has no
lower spiral number than the next square, after scaling by s. -/
theorem greedy (s p q e1 e2 : ℤ) (hs : 0 < s) (hpar : (p + q) % 2 = 0)
    (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
    (h : ¬ Before (p + e1) (q + e2) p q) :
    spiral (s * nx p q, s * ny p q) ≤ spiral (s * (p + e1), s * (q + e2)) := by
  have m1 : p + -1 = p - 1 := by grind
  have m2 : q + -1 = q - 1 := by grind
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl
  · exact greedy_pp s p q hs hpar h
  · rw [m2] at h ⊢; exact greedy_pm s p q hs hpar h
  · rw [m1] at h ⊢; exact greedy_mp s p q hs hpar h
  · rw [m1, m2] at h ⊢; exact greedy_mm s p q hs hpar h

end Leaper
