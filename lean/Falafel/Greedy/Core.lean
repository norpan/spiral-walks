import Falafel.Stamp
import Falafel.Tactic

/-!
# The greedy rule on the laps R ≥ 4: statement and proof script

For a square (u, v) with lap number R ≥ 4, move (a, b), and the neighbour at offset (c, d) with
lap number R': if the neighbour is visited later, then the spiral number of the square the walk
moves to is not above the neighbour's. One file per offset proves this for all squares.
-/
namespace Falafel

/-- The greedy rule for the neighbour at offset (c, d), for all squares of all laps R ≥ 4. -/
abbrev GreedyCore (c d : ℤ) : Prop :=
  ∀ u v a b R R' : ℤ,
    du u v = a → dv u v = b → lapnum u v = R → lapnum (u + c) (v + d) = R' → R ≥ 4 →
    (R < R' ∨ (R = R' ∧ posIn R u v < posIn R' (u + c) (v + d))) →
    KeyLE (u + a) (v + b) (u + c) (v + d)

/-- Three rounds of case analysis: the move, then the two lap numbers, then the indices and the
ring positions. A neighbour in an earlier lap is dismissed before the third round. -/
macro "greedy_core" : tactic =>
  `(tactic| (
    intro u v a b R R'
    unfold du dv
    split_cases
    all_goals (intro ha hb; subst ha hb; unfold lapnum; simp only [Int.add_zero]; split_cases)
    all_goals (intro hR hR'; subst hR hR')
    all_goals (first
      | (intro h4 hl; exfalso; omega)
      | (unfold KeyLE ring rpos posIn; split_omega))))

end Falafel
