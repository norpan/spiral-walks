import LeaperStatement
import Leaper.Theorems
import Leaper.Check

/-!
# The Ferz walk (OEIS A316884) and the Alfil walk (OEIS A317467) never end

Root of the library. The theorems are in `Leaper/Theorems.lean`; their statements are the four
definitions at the end of `LeaperStatement.lean`.

Below: the axioms they depend on. `sorryAx` would mean an unfinished proof, and
`Lean.ofReduceBool` or `Lean.trustCompiler` would mean `native_decide`.
-/

#print axioms Leaper.deterministic
#print axioms Leaper.never_trapped
#print axioms Leaper.visits_exactly_reachable_squares
#print axioms Leaper.ferz_permutation_of_odd_numbers
#print axioms Leaper.ferz_never_trapped
#print axioms Leaper.alfil_never_trapped
#print axioms Leaper.walk_eq_iff
#print axioms Leaper.ferz_first_terms
#print axioms Leaper.alfil_first_terms
