import Falafel.Laps
import Falafel.Step
import Falafel.Greedy
import Falafel.Prefix

/-!
# All squares

The facts about the first 80 squares and about the laps, put together: statements about every
square (u, v), in terms of `lap`, `idx`, `stepu`, `stepv`.
-/
namespace Falafel

theorem lap_low {u v : ℤ} (h : lapnum u v ≤ 3) : lap u v = 3 := ite_eq_left h
theorem lap_big {u v : ℤ} (h : ¬ lapnum u v ≤ 3) : lap u v = lapnum u v := ite_eq_right h
theorem idx_low {u v : ℤ} (h : lapnum u v ≤ 3) : idx u v = (pidx u v : ℤ) := ite_eq_left h
theorem idx_big {u v : ℤ} (h : ¬ lapnum u v ≤ 3) : idx u v = pos u v := ite_eq_right h
theorem lolap_big {R : ℤ} (h : ¬ R ≤ 3) : lolap R = lo R := ite_eq_right h
theorem hilap_big {R : ℤ} (h : ¬ R ≤ 3) : hilap R = hi R := ite_eq_right h
theorem stepu_big {u v : ℤ} (h : ¬ lapnum u v ≤ 3) : stepu u v = u + du u v :=
  ite_eq_right (fun hh => h hh.1)
theorem stepv_big {u v : ℤ} (h : ¬ lapnum u v ≤ 3) : stepv u v = v + dv u v :=
  ite_eq_right (fun hh => h hh.1)

/-- Laps start at 3. -/
theorem lap_ge (u v : ℤ) : 3 ≤ lap u v := by
  unfold lap
  split_ifs <;> omega

/-- The index is within the lap. -/
theorem idx_range (u v : ℤ) : lolap (lap u v) ≤ idx u v ∧ idx u v < hilap (lap u v) := by
  by_cases h : lapnum u v ≤ 3
  · have hm := (prefix_mem u v h).1
    rw [idx_low h, lap_low h]
    simp only [lolap, hilap]
    omega
  · have hr := pos_range u v (by omega)
    rw [idx_big h, lap_big h, lolap_big h, hilap_big h]
    exact hr

/-- Different squares have different stamps. -/
theorem stamp_inj (u v u' v' : ℤ) (hl : lap u v = lap u' v') (hi : idx u v = idx u' v') :
    u = u' ∧ v = v' := by
  by_cases h : lapnum u v ≤ 3
  · by_cases h' : lapnum u' v' ≤ 3
    · rw [idx_low h, idx_low h'] at hi
      have hp : pidx u v = pidx u' v' := by exact_mod_cast hi
      have e := (prefix_mem u v h).2
      rw [hp, (prefix_mem u' v' h').2] at e
      exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · rw [lap_low h, lap_big h'] at hl
      omega
  · by_cases h' : lapnum u' v' ≤ 3
    · rw [lap_big h, lap_low h'] at hl
      omega
    · rw [lap_big h, lap_big h'] at hl
      rw [idx_big h, idx_big h'] at hi
      have a := sq_pos u v (by omega)
      have b := sq_pos u' v' (by omega)
      rw [hl, hi] at a
      omega

/-- The step leads to the next stamp. -/
theorem step_ok (u v : ℤ) : StepOK u v := by
  by_cases h : lapnum u v ≤ 3
  · exact (prefix_ok u v h).1
  · have hb := step_big u v (by omega)
    have h' : ¬ lapnum (u + du u v) (v + dv u v) ≤ 3 := by omega
    have h'' : ¬ lapnum u v + 1 ≤ 3 := by omega
    unfold StepOK
    rw [stepu_big h, stepv_big h, lap_big h, idx_big h, lap_big h', idx_big h', lolap_big h'',
      hilap_big h]
    exact hb

/-- The step is a rook move of 1 or 2 squares. -/
theorem rook_ok (u v : ℤ) : Rook (stepu u v - u) (stepv u v - v) := by
  by_cases h : lapnum u v ≤ 3
  · exact (prefix_ok u v h).2.1
  · have hb := rook_big u v (by omega)
    rw [stepu_big h, stepv_big h]
    unfold Rook at hb ⊢
    omega

theorem greedy_of_big (u v c d : ℤ) (h : ¬ lapnum u v ≤ 3) (hb : GreedyBig u v c d) :
    Greedy u v c d := by
  intro hl
  unfold Later at hl
  rw [stepu_big h, stepv_big h]
  rw [lap_big h, idx_big h] at hl
  by_cases h' : lapnum (u + c) (v + d) ≤ 3
  · rw [lap_low h'] at hl
    omega
  · rw [lap_big h', idx_big h'] at hl
    exact hb (by omega) hl

theorem all_greedy (u v : ℤ) : AllGreedy u v := by
  by_cases h : lapnum u v ≤ 3
  · exact (prefix_ok u v h).2.2
  · exact ⟨greedy_of_big u v _ _ h (greedyBig_of_core greedy_e1 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_w1 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_e2 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_w2 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_n1 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_s1 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_n2 u v),
      greedy_of_big u v _ _ h (greedyBig_of_core greedy_s2 u v)⟩

/-- The greedy rule: a neighbour that is visited later does not have a lower spiral number than
the square the walk moves to. -/
theorem greedy (u v c d : ℤ) (hr : Rook c d) : Greedy u v c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := all_greedy u v
  rcases hr with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;> assumption

end Falafel
