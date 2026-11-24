import Falafel.Greedy.Core

/-! The greedy rule for the neighbour at offset (2, 0). -/
namespace Falafel

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

theorem greedy_e2 : GreedyCore (2) (0) := by greedy_core

end Falafel
