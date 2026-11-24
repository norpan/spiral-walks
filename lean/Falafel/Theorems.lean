import Statement
import Falafel.Main

/-!
# The four theorems

Their statements are the four definitions at the end of `Statement.lean`, in the same order.
Each is one statement of the paper.
-/
namespace Falafel

/-- **Remark 1. There is at most one infinite run of the walk.** -/
theorem deterministic : Deterministic :=
  fun a b ha hb => (walk_unique a ha).trans (walk_unique b hb).symm

/-- **Theorem 1 (a). The Falafel walk (OEIS A399160) is never trapped.** -/
theorem never_trapped : NeverTrapped :=
  ⟨walk, walk_isWalk⟩

/-- **Theorem 1 (b). The walk visits every square (x, y) with x + y even, and no other square.** -/
theorem visits_exactly_even_squares : VisitsExactlyEvenSquares := by
  intro a ha x y
  constructor
  · rintro ⟨n, hn⟩
    have h := walk_even n
    rw [← walk_unique a ha, hn] at h
    exact h
  · exact fun h => walk_unique a ha ▸ walk_visits x y h

/-- **Corollary 8. Every term is an odd positive integer, and every odd positive integer is a term
exactly once.** So A399160 is a permutation of the odd positive integers. -/
theorem permutation_of_odd_numbers : PermutationOfOddNumbers := by
  intro a ha
  obtain rfl := walk_unique a ha
  exact ⟨fun n => ⟨spiral_pos _ _, walk_term_odd n⟩, walk_term_unique⟩

end Falafel
