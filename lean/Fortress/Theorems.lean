import FortressStatement
import Fortress.Main

/-!
# The theorems

Their statements are the three definitions at the end of `FortressStatement.lean`. Below them:
the Fortress and the Alfilerzbaba as instances.
-/
namespace Fortress

open Falafel (spiral)
open Straight (IsWalk)

/-- **There is at most one infinite run of the walk.** -/
theorem deterministic : Deterministic :=
  fun M hM a b ha hb => (walk_unique M hM a ha).trans (walk_unique M hM b hb).symm

/-- **The piece is never trapped.** -/
theorem never_trapped : NeverTrapped :=
  fun M hM => ⟨walk, walk_isWalk M hM⟩

/-- **The walk is 1, 3, 5, ...** -/
theorem walks_odd_numbers : WalksOddNumbers := by
  intro M hM a ha n
  rw [walk_unique M hM a ha, spiral_walk]

/-- The moves of the Fortress: Ferz and Dabbaba. -/
def fortress : Set (ℤ × ℤ) :=
  {(1, 1), (1, -1), (-1, 1), (-1, -1), (2, 0), (-2, 0), (0, 2), (0, -2)}

/-- The moves of the Alfilerzbaba: Ferz, Dabbaba and Alfil. -/
def alfilerzbaba : Set (ℤ × ℤ) :=
  {(1, 1), (1, -1), (-1, 1), (-1, -1), (2, 0), (-2, 0), (0, 2), (0, -2),
   (2, 2), (2, -2), (-2, 2), (-2, -2)}

theorem fortress_moves : MovesLikeFortress fortress := by
  refine ⟨by simp [fortress], by simp [fortress], by simp [fortress], by simp [fortress],
    by simp [fortress], by simp [fortress], by simp [fortress], by simp [fortress], fun d hd => ?_⟩
  simp only [fortress, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem alfilerzbaba_moves : MovesLikeFortress alfilerzbaba := by
  refine ⟨by simp [alfilerzbaba], by simp [alfilerzbaba], by simp [alfilerzbaba],
    by simp [alfilerzbaba], by simp [alfilerzbaba], by simp [alfilerzbaba], by simp [alfilerzbaba],
    by simp [alfilerzbaba], fun d hd => ?_⟩
  simp only [alfilerzbaba, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Fortress walk is never trapped. -/
theorem fortress_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk fortress a :=
  never_trapped _ fortress_moves

/-- The Alfilerzbaba walk is never trapped. -/
theorem alfilerzbaba_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk alfilerzbaba a :=
  never_trapped _ alfilerzbaba_moves

/-- The Fortress and the Alfilerzbaba make the same walk. -/
theorem alfilerzbaba_eq_fortress (a b : ℕ → ℤ × ℤ) (ha : IsWalk fortress a)
    (hb : IsWalk alfilerzbaba b) : a = b :=
  (walk_unique _ fortress_moves a ha).trans (walk_unique _ alfilerzbaba_moves b hb).symm

end Fortress
