import Statement
import Falafel.Tactic

/-!
# The spiral numbers are the positive integers

Three facts about the spiral number of any square (x, y), not only the Falafel's squares:
it is positive, it is odd exactly if x + y is even, and every positive integer is the spiral
number of some square.
-/
namespace Falafel

/-- The ring r = max(|x|, |y|) without absolute values: the square is inside the box of
half-width r and on its border. -/
theorem ring_iff (x y r : ℤ) :
    max |x| |y| = r ↔
      (-r ≤ x ∧ x ≤ r) ∧ (-r ≤ y ∧ y ≤ r) ∧ (x = r ∨ x = -r ∨ y = r ∨ y = -r) := by
  abs_omega

/-- The spiral number of a square whose ring is known to be r. -/
theorem spiral_eq (x y r : ℤ) (h : max |x| |y| = r) :
    spiral (x, y) =
      if x = r ∧ y > -r then (2 * r - 1) ^ 2 + (y + r)
      else if y = r then (2 * r - 1) ^ 2 + 2 * r + (r - x)
      else if x = -r then (2 * r - 1) ^ 2 + 4 * r + (r - y)
      else (2 * r - 1) ^ 2 + 6 * r + (x + r) := by
  simp only [spiral, h]

/-- The first number of a ring, minus one, is an odd square. -/
theorem odd_square (r : ℤ) (hr : 0 ≤ r) : ∃ m, 0 ≤ m ∧ (2 * r - 1) ^ 2 = 2 * m + 1 :=
  ⟨2 * (r * r) - 2 * r, by
    rcases (show r = 0 ∨ 1 ≤ r by omega) with h | h
    · subst h; decide
    · have := Int.mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ r - 1 by omega); grind, by grind⟩

/-- **Parity.** The spiral number of (x, y) has the parity of x + y + 1. So the squares with
x + y even are exactly the odd-numbered squares. -/
theorem spiral_parity (x y : ℤ) : spiral (x, y) % 2 = (x + y + 1) % 2 := by
  obtain ⟨hx, hy, hb⟩ := (ring_iff x y _).mp rfl
  rw [spiral_eq x y _ rfl]
  generalize max |x| |y| = r at hx hy hb ⊢
  obtain ⟨m, -, hm⟩ := odd_square r (by omega)
  rw [hm]
  split_ifs <;> omega

/-- Spiral numbers are positive. -/
theorem spiral_pos (x y : ℤ) : 0 < spiral (x, y) := by
  obtain ⟨hx, hy, hb⟩ := (ring_iff x y _).mp rfl
  rw [spiral_eq x y _ rfl]
  generalize max |x| |y| = r at hx hy hb ⊢
  obtain ⟨m, h0, hm⟩ := odd_square r (by omega)
  rw [hm]
  split_ifs <;> omega

/-- Ring r ≥ 1 holds the numbers (2r - 1)² + 1 to (2r - 1)² + 8r. -/
theorem spiral_on_ring (r t : ℤ) (hr : 1 ≤ r) (h1 : 1 ≤ t) (h2 : t ≤ 8 * r) :
    ∃ p, spiral p = (2 * r - 1) ^ 2 + t := by
  by_cases c1 : t ≤ 2 * r
  · refine ⟨(r, t - r), ?_⟩
    rw [spiral_eq r (t - r) r ((ring_iff _ _ _).mpr (by omega))]
    split_ifs <;> omega
  by_cases c2 : t ≤ 4 * r
  · refine ⟨(3 * r - t, r), ?_⟩
    rw [spiral_eq (3 * r - t) r r ((ring_iff _ _ _).mpr (by omega))]
    split_ifs <;> omega
  by_cases c3 : t ≤ 6 * r
  · refine ⟨(-r, 5 * r - t), ?_⟩
    rw [spiral_eq (-r) (5 * r - t) r ((ring_iff _ _ _).mpr (by omega))]
    split_ifs <;> omega
  · refine ⟨(t - 7 * r, -r), ?_⟩
    rw [spiral_eq (t - 7 * r) (-r) r ((ring_iff _ _ _).mpr (by omega))]
    split_ifs <;> omega

/-- The least r with k ≤ (2r + 1)², found by going down from any such r. -/
theorem least_ring (k : ℤ) : ∀ N : ℕ, k ≤ (2 * (N : ℤ) + 1) ^ 2 →
    ∃ r : ℕ, k ≤ (2 * (r : ℤ) + 1) ^ 2 ∧ ∀ m < r, ¬ k ≤ (2 * (m : ℤ) + 1) ^ 2
  | 0, h => ⟨0, h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | N + 1, h => by
    by_cases h' : k ≤ (2 * (N : ℤ) + 1) ^ 2
    · exact least_ring k N h'
    · refine ⟨N + 1, h, fun m hm hm' => h' ?_⟩
      have := Int.mul_nonneg (show (0 : ℤ) ≤ N - m by omega) (show (0 : ℤ) ≤ N + m + 1 by omega)
      grind

/-- **Every positive integer is the spiral number of a square.** -/
theorem spiral_surjective (k : ℤ) (hk : 0 < k) : ∃ p, spiral p = k := by
  obtain ⟨r, hr, hmin⟩ := least_ring k k.toNat (by
    rw [Int.toNat_of_nonneg (Int.le_of_lt hk)]
    have := Int.mul_nonneg (show (0 : ℤ) ≤ k by omega) (show (0 : ℤ) ≤ k by omega); grind)
  rcases r with _ | r
  · obtain rfl : k = 1 := by
      have : (2 * ((0 : ℕ) : ℤ) + 1) ^ 2 = 1 := by decide
      omega
    exact ⟨(0, 0), by decide⟩
  · have hlow := hmin r (Nat.lt_succ_self r)
    push_cast at hr
    have e1 : (2 * ((r : ℤ) + 1) + 1) ^ 2 = (2 * ((r : ℤ) + 1) - 1) ^ 2 + 8 * ((r : ℤ) + 1) := by
      grind
    have e2 : (2 * (r : ℤ) + 1) ^ 2 = (2 * ((r : ℤ) + 1) - 1) ^ 2 := by grind
    obtain ⟨p, hp⟩ := spiral_on_ring ((r : ℤ) + 1) (k - (2 * ((r : ℤ) + 1) - 1) ^ 2)
      (by omega) (by omega) (by omega)
    exact ⟨p, by rw [hp]; omega⟩

end Falafel
