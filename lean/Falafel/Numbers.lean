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
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2, max_def] <;> split_ifs <;> omega

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
  ⟨2 * (r * r) - 2 * r, by nlinarith, by ring⟩

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

/-- **Every positive integer is the spiral number of a square.** -/
theorem spiral_surjective (k : ℤ) (hk : 0 < k) : ∃ p, spiral p = k := by
  have hex : ∃ r : ℕ, k ≤ (2 * (r : ℤ) + 1) ^ 2 :=
    ⟨k.toNat, by rw [Int.toNat_of_nonneg hk.le]; nlinarith⟩
  obtain ⟨r, hr, hmin⟩ :
      ∃ r : ℕ, k ≤ (2 * (r : ℤ) + 1) ^ 2 ∧ ∀ m < r, ¬ k ≤ (2 * (m : ℤ) + 1) ^ 2 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  rcases r with _ | r
  · obtain rfl : k = 1 := by norm_num at hr; omega
    exact ⟨(0, 0), by decide⟩
  · have hlow := hmin r (Nat.lt_succ_self r)
    push_cast at hr
    have e1 : (2 * ((r : ℤ) + 1) + 1) ^ 2 = (2 * ((r : ℤ) + 1) - 1) ^ 2 + 8 * ((r : ℤ) + 1) := by
      ring
    have e2 : (2 * (r : ℤ) + 1) ^ 2 = (2 * ((r : ℤ) + 1) - 1) ^ 2 := by ring
    obtain ⟨p, hp⟩ := spiral_on_ring ((r : ℤ) + 1) (k - (2 * ((r : ℤ) + 1) - 1) ^ 2)
      (by omega) (by linarith) (by linarith)
    exact ⟨p, by rw [hp]; ring⟩

end Falafel
