import Statement
import Falafel.Main

/-!
# The walk against the OEIS data

A check that `Statement.lean` describes A399160: the spiral numbers of the first 70 squares of
the walk are the 70 terms in the DATA section of the OEIS entry. Since the walk is the only
sequence that satisfies `IsWalk` (`deterministic`), this pins the definition to the entry.
The check is by evaluation in the kernel.
-/
namespace Falafel

/-- The DATA section of A399160, as fetched from oeis.org on 23 Nov 2026. -/
def oeisData : List ℤ :=
  [1, 3, 7, 19, 5, 9, 11, 15, 33, 13, 29, 53, 25, 27, 47, 23, 45, 21, 41, 69, 17, 35, 39, 67, 37,
   63, 97, 61, 95, 31, 55, 59, 93, 57, 89, 129, 87, 127, 51, 49, 79, 117, 77, 115, 43, 71, 75,
   113, 73, 109, 153, 107, 151, 105, 149, 65, 99, 103, 147, 101, 143, 193, 141, 191, 139, 189,
   137, 187, 91, 131]

/-- The first 70 terms of the walk are the OEIS terms. -/
theorem first_terms : (List.range 70).map (fun n => spiral (walk n)) = oeisData := by
  decide +kernel

end Falafel
