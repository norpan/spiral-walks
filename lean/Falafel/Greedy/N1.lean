import Falafel.Greedy.Core

/-! The greedy rule for the neighbour at offset (0, 1). -/
namespace Falafel

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

theorem greedy_n1 : GreedyCore (0) (1) := by greedy_core

end Falafel
