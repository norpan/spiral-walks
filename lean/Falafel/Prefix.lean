import Falafel.Stamp
import Falafel.Tactic

/-!
# The first 80 squares, by computation

The facts the main proof needs about each of the first 80 squares are decidable. They are
checked by evaluation in the kernel (`decide`), not by `native_decide`.
-/
namespace Falafel

/-- The step from (u, v) leads to the next index of its lap, or from the last index of a lap to
the first index of the next lap. -/
def StepOK (u v : ℤ) : Prop :=
  (lap (stepu u v) (stepv u v) = lap u v ∧ idx (stepu u v) (stepv u v) = idx u v + 1) ∨
  (lap (stepu u v) (stepv u v) = lap u v + 1 ∧
    idx (stepu u v) (stepv u v) = lolap (lap u v + 1) ∧ idx u v + 1 = hilap (lap u v))

instance (u v : ℤ) : Decidable (StepOK u v) := by unfold StepOK; infer_instance

/-- The greedy rule at (u, v) for the neighbour at offset (c, d). -/
def Greedy (u v c d : ℤ) : Prop :=
  Later (u + c) (v + d) u v → KeyLE (stepu u v) (stepv u v) (u + c) (v + d)

instance (u v c d : ℤ) : Decidable (Greedy u v c d) := by unfold Greedy; infer_instance

/-- The greedy rule at (u, v) for all 8 neighbours. -/
def AllGreedy (u v : ℤ) : Prop :=
  Greedy u v 1 0 ∧ Greedy u v (-1) 0 ∧ Greedy u v 2 0 ∧ Greedy u v (-2) 0 ∧
  Greedy u v 0 1 ∧ Greedy u v 0 (-1) ∧ Greedy u v 0 2 ∧ Greedy u v 0 (-2)

instance (u v : ℤ) : Decidable (AllGreedy u v) := by unfold AllGreedy; infer_instance

/-- Everything needed about one square. -/
def SquareOK (u v : ℤ) : Prop :=
  StepOK u v ∧ Rook (stepu u v - u) (stepv u v - v) ∧ AllGreedy u v

instance (u v : ℤ) : Decidable (SquareOK u v) := by unfold SquareOK; infer_instance

/-- The table is consistent, and every one of the first 80 squares is in order. -/
theorem prefix_table : ∀ i < 80,
    lapnum (pget i).1 (pget i).2 ≤ 3 ∧ pidx (pget i).1 (pget i).2 = i ∧
      SquareOK (pget i).1 (pget i).2 := by
  decide +kernel

/-- Every square of the box -4 ≤ u ≤ 6, -5 ≤ v ≤ 4 with lap number at most 3 is in the table. -/
theorem prefix_box : ∀ u ∈ Finset.Icc (-4 : ℤ) 6, ∀ v ∈ Finset.Icc (-5 : ℤ) 4,
    lapnum u v ≤ 3 → pidx u v < 80 ∧ pget (pidx u v) = (u, v) := by
  decide +kernel

/-- Squares with lap number at most 3 lie in that box. -/
theorem low_bounds (u v : ℤ) : lapnum u v ≤ 3 → -4 ≤ u ∧ u ≤ 6 ∧ -5 ≤ v ∧ v ≤ 4 := by
  unfold lapnum
  split_omega

/-- A square with lap number at most 3 is one of the first 80 squares. -/
theorem prefix_mem (u v : ℤ) (h : lapnum u v ≤ 3) : pidx u v < 80 ∧ pget (pidx u v) = (u, v) := by
  obtain ⟨h1, h2, h3, h4⟩ := low_bounds u v h
  exact prefix_box u (Finset.mem_Icc.mpr ⟨h1, h2⟩) v (Finset.mem_Icc.mpr ⟨h3, h4⟩) h

/-- Every square with lap number at most 3 is in order. -/
theorem prefix_ok (u v : ℤ) (h : lapnum u v ≤ 3) : SquareOK u v := by
  obtain ⟨hi, hg⟩ := prefix_mem u v h
  have h3 := (prefix_table (pidx u v) hi).2.2
  rw [hg] at h3
  exact h3

end Falafel
