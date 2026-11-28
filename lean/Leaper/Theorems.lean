import LeaperStatement
import Leaper.Main

/-!
# The theorems

Their statements are the four definitions at the end of `LeaperStatement.lean`. The first three
are for every leap length s > 0. The Ferz is s = 1 and the Alfil is s = 2.
-/
namespace Leaper

open Falafel (spiral)

/-- **There is at most one infinite run of the walk.** -/
theorem deterministic : Deterministic :=
  fun s hs a b ha hb => (walk_unique s hs a ha).trans (walk_unique s hs b hb).symm

/-- **The walk of the (s, s)-leaper is never trapped.** -/
theorem never_trapped : NeverTrapped :=
  fun s hs => ⟨walk s, walk_isWalk s hs⟩

/-- **The walk visits exactly the squares (s i, s j) with i + j even.** -/
theorem visits_exactly_reachable_squares : VisitsExactlyReachableSquares := by
  intro s hs a ha x y
  rw [walk_unique s hs a ha]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(w n).1, (w n).2, Int.even_iff.mpr (w_par n), (congrArg Prod.fst hn).symm,
      (congrArg Prod.snd hn).symm⟩
  · rintro ⟨i, j, hij, rfl, rfl⟩
    exact ⟨(rk i j).toNat, by rw [walk, w_of_rk i j (Int.even_iff.mp hij)]⟩

/-- **A316884, the Ferz walk, is a permutation of the odd positive integers.** -/
theorem ferz_permutation_of_odd_numbers : FerzPermutationOfOddNumbers := by
  intro a ha
  rw [walk_unique 1 Int.one_pos a ha]
  have hodd : ∀ n, Odd (spiral (walk 1 n)) := fun n => by
    have h := Falafel.spiral_parity (1 * (w n).1) (1 * (w n).2)
    have hp := w_par n
    exact Int.odd_iff.mpr (by rw [walk]; omega)
  refine ⟨fun n => ⟨Falafel.spiral_pos _ _, hodd n⟩, fun k hk hk' => ?_⟩
  obtain ⟨⟨x, y⟩, hp⟩ := Falafel.spiral_surjective k hk
  have hpar : (x + y) % 2 = 0 := by
    have h := Falafel.spiral_parity x y
    rw [hp] at h
    have := Int.odd_iff.mp hk'
    omega
  refine ⟨(rk x y).toNat, ?_, fun m hm => ?_⟩
  · show spiral (walk 1 (rk x y).toNat) = k
    rw [walk, w_of_rk x y hpar, Int.one_mul, Int.one_mul, hp]
  · have e : walk 1 m = walk 1 (rk x y).toNat := by
      apply spiral_inj'
      rw [hm, walk, w_of_rk x y hpar, Int.one_mul, Int.one_mul, hp]
    exact walk_injective 1 Int.one_pos e

/-- The Ferz walk (OEIS A316884) is never trapped. -/
theorem ferz_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk 1 a := never_trapped 1 Int.one_pos

/-- The Alfil walk (OEIS A317467) is never trapped. -/
theorem alfil_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk 2 a := never_trapped 2 (by decide : (0:ℤ) < 2)

end Leaper
