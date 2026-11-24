import Statement
import Falafel.Theorems
import Falafel.Check
import Falafel.Start
import Falafel.Terms

/-!
# The Falafel walk (OEIS A399160) never ends

Root of the library. The four theorems are in `Falafel/Theorems.lean`; their statements are the
four definitions at the end of `Statement.lean`.

Below: the axioms they depend on. `sorryAx` would mean an unfinished proof, and
`Lean.ofReduceBool` or `Lean.trustCompiler` would mean `native_decide`.
-/

#print axioms Falafel.deterministic
#print axioms Falafel.never_trapped
#print axioms Falafel.visits_exactly_even_squares
#print axioms Falafel.permutation_of_odd_numbers
#print axioms Falafel.walk_follows_path
#print axioms Falafel.walk_follows_path_from_start
#print axioms Falafel.walk_eq_path
#print axioms Falafel.term_formula
#print axioms Falafel.lapnum_eq_iff
#print axioms Falafel.lapnum_le_three_iff
#print axioms Falafel.first_terms
