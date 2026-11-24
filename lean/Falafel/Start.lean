import PathStatement
import Falafel.Main

/-!
# The step at which each lap starts

`walk_follows_path` in `Main.lean` says that lap R starts "at some step n". Here the step is
given: lap R ≥ 4 starts at step `start R`. With it the closed-form path gives the square of every
step n ≥ 80 (Corollary 9 of the paper).
-/
namespace Falafel

theorem start_even (m : ℤ) : start (2 * m) = 27 * m ^ 2 - 11 * m - 6 := by
  unfold start
  have h : (2 * m) % 2 = 0 := by omega
  rw [h, show 27 * (2 * m) ^ 2 - 22 * (2 * m) - 24 - 9 * 0 = 4 * (27 * m ^ 2 - 11 * m - 6) by ring]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem start_odd (m : ℤ) : start (2 * m + 1) = 27 * m ^ 2 + 16 * m - 7 := by
  unfold start
  have h : (2 * m + 1) % 2 = 1 := by omega
  rw [h, show 27 * (2 * m + 1) ^ 2 - 22 * (2 * m + 1) - 24 - 9 * 1
    = 4 * (27 * m ^ 2 + 16 * m - 7) by ring]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- The starts of two consecutive laps differ by the length of the lap. -/
theorem start_succ (R : ℤ) : start (R + 1) = start R + (hi R - lo R) := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' R
  · have hl : hi (2 * m) - lo (2 * m) = 27 * m - 1 := by unfold hi lo; omega
    rw [start_odd, start_even, hl]
    ring
  · have hl : hi (2 * m + 1) - lo (2 * m + 1) = 27 * m + 17 := by unfold hi lo; omega
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, start_even, start_odd, hl]
    ring

/-- From the first index of a lap, the walk is at the first index of the next lap after as many
steps as the lap has indices. -/
theorem next_lap (n : ℕ) (hJ : J n = lolap (L n)) :
    L (n + (hilap (L n) - lolap (L n)).toNat) = L n + 1 ∧
      J (n + (hilap (L n) - lolap (L n)).toNat) = lolap (L n + 1) := by
  have hr0 := LJ_range n
  have hc : ((hilap (L n) - 1 - lolap (L n)).toNat : ℤ) = hilap (L n) - 1 - lolap (L n) :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨h1, h2⟩ := run_lap n hJ (hilap (L n) - 1 - lolap (L n)).toNat (by omega)
  have hs := LJ_succ (n + (hilap (L n) - 1 - lolap (L n)).toNat)
  have hr := LJ_range (n + (hilap (L n) - 1 - lolap (L n)).toNat + 1)
  have he : n + (hilap (L n) - lolap (L n)).toNat
      = n + (hilap (L n) - 1 - lolap (L n)).toNat + 1 := by omega
  rw [he]
  rcases hs with ⟨e1, e2⟩ | ⟨e1, e2, -⟩
  · rw [e1, h1] at hr
    omega
  · rw [h1] at e1 e2
    exact ⟨e1, e2⟩

/-- Lap 4 + k starts at step `start (4 + k)`. -/
theorem lap_start (k : ℕ) :
    0 ≤ start (4 + k) ∧ L (start (4 + k)).toNat = 4 + k ∧ J (start (4 + k)).toNat = lo (4 + k) := by
  induction k with
  | zero =>
    have hs : start (4 + ((0 : ℕ) : ℤ)) = 80 := by decide
    have h := next_lap 0 (by decide)
    rw [L_zero] at h
    have e : (hilap 3 - lolap 3).toNat = 80 := by decide
    have e4 : lolap (3 + 1) = lo (4 + ((0 : ℕ) : ℤ)) := by decide
    rw [e, Nat.zero_add, e4] at h
    rw [hs]
    exact ⟨by norm_num, by simpa using h.1, h.2⟩
  | succ k ih =>
    obtain ⟨h0, hL, hJ⟩ := ih
    have h3 : ¬ (4 + (k : ℤ)) ≤ 3 := by omega
    have h3' : ¬ (4 + (k : ℤ) + 1) ≤ 3 := by omega
    have h := next_lap (start (4 + k)).toNat (by rw [hL, lolap_big h3]; exact hJ)
    rw [hL, hilap_big h3, lolap_big h3, lolap_big h3'] at h
    have hlen : 0 ≤ hi (4 + (k : ℤ)) - lo (4 + (k : ℤ)) := by unfold hi lo; omega
    have hcast : (4 : ℤ) + ((k + 1 : ℕ) : ℤ) = 4 + (k : ℤ) + 1 := by push_cast; ring
    rw [hcast, start_succ, Int.toNat_add h0 hlen]
    exact ⟨by omega, h.1, h.2⟩

/-- **Lap R ≥ 4 starts at step `start R`.** From there the walk runs through the squares
`(squ R j, sqv R j)` for j = lo R, ..., hi R - 1 in order. -/
theorem walk_follows_path_from_start (R : ℤ) (hR : 4 ≤ R) (j : ℕ) (hj : lo R + j < hi R) :
    w ((start R).toNat + j) = (squ R (lo R + j), sqv R (lo R + j)) := by
  obtain ⟨-, hL, hJ⟩ := lap_start (R - 4).toNat
  have hc : 4 + ((R - 4).toNat : ℤ) = R := by omega
  rw [hc] at hL hJ
  have h3 : ¬ R ≤ 3 := by omega
  obtain ⟨h1, h2⟩ := run_lap (start R).toNat (by rw [hL, lolap_big h3]; exact hJ) j
    (by rw [hL, lolap_big h3, hilap_big h3]; exact hj)
  rw [hL] at h1
  rw [hL, lolap_big h3] at h2
  have hbig : ¬ lapnum (w ((start R).toNat + j)).1 (w ((start R).toNat + j)).2 ≤ 3 :=
    fun hlow => by
      have h4 : L ((start R).toNat + j) = 3 := lap_low hlow
      omega
  have e1 : lapnum (w ((start R).toNat + j)).1 (w ((start R).toNat + j)).2 = R := by
    rw [← lap_big hbig]; exact h1
  have e2 : pos (w ((start R).toNat + j)).1 (w ((start R).toNat + j)).2 = lo R + j := by
    rw [← idx_big hbig]; exact h2
  have hs := sq_pos (w ((start R).toNat + j)).1 (w ((start R).toNat + j)).2 (by omega)
  rw [e1, e2] at hs
  exact Prod.ext hs.1.symm hs.2.symm

/-- **Corollary 9. The square of every step n ≥ 80.** If lap R ≥ 4 has started at step n and
lap R + 1 has not, then the n-th square of the walk is the square at index lo R + (n - start R)
of the closed-form path of lap R. -/
theorem walk_eq_path (R : ℤ) (hR : 4 ≤ R) (n : ℕ) (h1 : start R ≤ n) (h2 : n < start (R + 1)) :
    w n = (squ R (lo R + (n - start R)), sqv R (lo R + (n - start R))) := by
  obtain ⟨h0, -, -⟩ := lap_start (R - 4).toNat
  have hc : 4 + ((R - 4).toNat : ℤ) = R := by omega
  rw [hc] at h0
  rw [start_succ] at h2
  have hj : (((n : ℤ) - start R).toNat : ℤ) = n - start R := Int.toNat_of_nonneg (by omega)
  have key := walk_follows_path_from_start R hR ((n : ℤ) - start R).toNat (by omega)
  have hn : (start R).toNat + ((n : ℤ) - start R).toNat = n := by omega
  rw [hj, hn] at key
  exact key

/-- Lap 4 starts at step 80 and lap 5 at step 133. -/
example : start 4 = 80 ∧ start 5 = 133 := by decide

end Falafel
