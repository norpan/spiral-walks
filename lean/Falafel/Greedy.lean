import Falafel.Greedy.E1
import Falafel.Greedy.W1
import Falafel.Greedy.E2
import Falafel.Greedy.W2
import Falafel.Greedy.N1
import Falafel.Greedy.S1
import Falafel.Greedy.N2
import Falafel.Greedy.S2

/-!
# The greedy rule on the laps R ≥ 4, for all 8 neighbours
-/
namespace Falafel

/-- The greedy rule at a square of a lap, for the neighbour at offset (c, d): if the neighbour is
visited later, its spiral number is not below that of the square the walk moves to. -/
abbrev GreedyBig (u v c d : ℤ) : Prop :=
  lapnum u v ≥ 4 →
  (lapnum u v < lapnum (u + c) (v + d) ∨
    (lapnum u v = lapnum (u + c) (v + d) ∧ pos u v < pos (u + c) (v + d))) →
  KeyLE (u + du u v) (v + dv u v) (u + c) (v + d)

theorem greedyBig_of_core {c d : ℤ} (h : GreedyCore c d) (u v : ℤ) : GreedyBig u v c d :=
  fun h4 hl => h u v _ _ _ _ rfl rfl rfl rfl h4 hl

end Falafel
