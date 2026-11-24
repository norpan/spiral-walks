import StraightStatement
import Straight.Theorems

/-!
# Pieces that can move straight never get trapped

Root of the library. The theorems are in `Straight/Theorems.lean`; their statements are the four
definitions at the end of `StraightStatement.lean`.

Below: the axioms they depend on. `sorryAx` would mean an unfinished proof, and
`Lean.ofReduceBool` or `Lean.trustCompiler` would mean `native_decide`.
-/

#print axioms Straight.deterministic
#print axioms Straight.never_trapped
#print axioms Straight.visits_lattice_in_order
#print axioms Straight.wazir_walks_in_order
#print axioms Straight.wazir_never_trapped
#print axioms Straight.dabbaba_never_trapped
#print axioms Straight.alibaba_never_trapped
#print axioms Straight.alibaba_eq_dabbaba
