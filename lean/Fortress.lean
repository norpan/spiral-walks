import FortressStatement
import Fortress.Theorems

/-!
# The Fortress and the Alfilerzbaba walk 1, 3, 5, ...

Root of the library. The theorems are in `Fortress/Theorems.lean`; their statements are the three
definitions at the end of `FortressStatement.lean`.

Below: the axioms they depend on. `sorryAx` would mean an unfinished proof, and
`Lean.ofReduceBool` or `Lean.trustCompiler` would mean `native_decide`.
-/

#print axioms Fortress.deterministic
#print axioms Fortress.never_trapped
#print axioms Fortress.walks_odd_numbers
#print axioms Fortress.fortress_never_trapped
#print axioms Fortress.alfilerzbaba_never_trapped
#print axioms Fortress.alfilerzbaba_eq_fortress
