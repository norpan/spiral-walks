import Falafel.Stamp
import Falafel.Tactic

/-!
# The laps R ≥ 4, for all R at once: range, moves, and the inverse map

Every statement here is about all squares with lap number at least 4. The proofs split into the
regions of `lapnum` and close each case with `omega`. There is no bound on R anywhere.
-/
namespace Falafel

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

/-- The index within the lap is in range. -/
theorem pos_range (u v : ℤ) :
    lapnum u v ≥ 4 → lo (lapnum u v) ≤ pos u v ∧ pos u v < hi (lapnum u v) := by
  unfold pos posIn lo hi lapnum
  split_omega

/-- The move is a rook move of 1 or 2 squares. -/
theorem rook_big (u v : ℤ) : lapnum u v ≥ 4 → Rook (du u v) (dv u v) := by
  unfold Rook lapnum du dv
  split_omega

/-- The closed-form path `(squ, sqv)` inverts `(lapnum, pos)`. So two different squares never
have the same lap number and index. -/
theorem sq_pos (u v : ℤ) :
    lapnum u v ≥ 4 → squ (lapnum u v) (pos u v) = u ∧ sqv (lapnum u v) (pos u v) = v := by
  unfold squ sqv pos posIn lapnum
  split_omega

end Falafel
