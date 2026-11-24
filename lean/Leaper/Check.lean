import LeaperStatement
import Leaper.Main

/-!
# The walks against the OEIS data

A check that `LeaperStatement.lean` describes A316884 (s = 1) and A317467 (s = 2): the spiral
numbers of the first squares of the walk are the terms in the DATA sections of the two OEIS
entries. Since the walk is the only sequence that satisfies `IsWalk s` (`deterministic`), this
pins the definition to the entries. The check is by evaluation in the kernel.
-/
namespace Leaper

open Falafel (spiral)

/-- The DATA section of A316884, as fetched from oeis.org on 24 Nov 2026. -/
def ferzData : List ℤ :=
  [1, 3, 11, 9, 23, 7, 19, 5, 15, 33, 13, 29, 53, 27, 25, 47, 77, 45, 21, 41, 69, 39, 17, 35, 61,
   95, 59, 31, 55, 87, 127, 85, 51, 49, 79, 117, 163, 115, 75, 43, 71, 107, 151, 105, 67, 37, 63,
   97, 139, 189, 137, 93, 57, 89, 129, 177, 233, 175, 125, 83, 81, 119]

/-- The DATA section of A317467, as fetched from oeis.org on 24 Nov 2026. -/
def alfilData : List ℤ :=
  [1, 13, 53, 25, 77, 21, 69, 17, 61, 137, 57, 129, 233, 125, 81, 165, 281, 161, 73, 153, 265,
   149, 65, 141, 249, 389, 245, 133, 237, 373, 541, 369, 229, 169, 285, 433, 613, 429, 277, 157,
   269, 413, 589, 409, 261, 145, 253, 393, 565, 769, 561, 385, 241, 377]

/-- The first 62 terms of the Ferz walk are the OEIS terms of A316884. -/
theorem ferz_first_terms : (List.range 62).map (fun n => spiral (walk 1 n)) = ferzData := by
  decide +kernel

/-- The first 54 terms of the Alfil walk are the OEIS terms of A317467. -/
theorem alfil_first_terms : (List.range 54).map (fun n => spiral (walk 2 n)) = alfilData := by
  decide +kernel

end Leaper
