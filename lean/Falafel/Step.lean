import Falafel.Stamp
import Falafel.Tactic

/-!
# The laps R ≥ 4: the move leads to the next index

Proved for all squares with lap number at least 4, in three rounds of case analysis: the move
`(a, b)`, then the lap numbers `R` and `R'` of the square and of its successor, then the indices.
-/
namespace Falafel

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

theorem step_core (u v a b R R' : ℤ) :
    du u v = a → dv u v = b → lapnum u v = R → lapnum (u + a) (v + b) = R' → R ≥ 4 →
    (R' = R ∧ posIn R' (u + a) (v + b) = posIn R u v + 1) ∨
    (R' = R + 1 ∧ posIn R' (u + a) (v + b) = lo (R + 1) ∧ posIn R u v + 1 = hi R) := by
  unfold du dv
  split_cases
  all_goals (intro ha hb; subst ha hb; unfold lapnum; simp only [Int.add_zero]; split_cases)
  all_goals (intro hR hR'; subst hR hR'; unfold posIn lo hi; split_omega)

/-- The move from a square leads to the next index of the same lap, or from the last index of a
lap to the first index of the next lap. -/
theorem step_big (u v : ℤ) (h : lapnum u v ≥ 4) :
    (lapnum (u + du u v) (v + dv u v) = lapnum u v ∧
      pos (u + du u v) (v + dv u v) = pos u v + 1) ∨
    (lapnum (u + du u v) (v + dv u v) = lapnum u v + 1 ∧
      pos (u + du u v) (v + dv u v) = lo (lapnum u v + 1) ∧ pos u v + 1 = hi (lapnum u v)) :=
  step_core u v _ _ _ _ rfl rfl rfl rfl h

end Falafel
