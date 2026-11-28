import StraightStatement
import Straight.Main

/-!
# The theorems

Their statements are the four definitions at the end of `StraightStatement.lean`. Below them:
the Wazir, the Dabbaba and the Alibaba as instances.
-/
namespace Straight

open Falafel (spiral)

/-- **There is at most one infinite run of the walk.** -/
theorem deterministic : Deterministic :=
  fun s hs M hM a b ha hb => (walk_unique s hs M hM a ha).trans (walk_unique s hs M hM b hb).symm

/-- **A piece that can move straight is never trapped.** -/
theorem never_trapped : NeverTrapped :=
  fun s hs M hM => ⟨walk s, walk_isWalk s hs M hM⟩

/-- **The walk visits exactly the squares with both coordinates multiples of s, in the order of
their numbers.** -/
theorem visits_lattice_in_order : VisitsLatticeInOrder := by
  intro s hs M hM a ha
  rw [walk_unique s hs M hM a ha]
  refine ⟨fun x y => ⟨?_, ?_⟩, walk_strictMono s hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨(w n).1, (congrArg Prod.fst hn).symm⟩, ⟨(w n).2, (congrArg Prod.snd hn).symm⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact ⟨(spiral (i, j) - 1).toNat, by unfold walk; rw [w_of_spiral (i, j)]⟩

/-- **A piece that has the Wazir's moves walks 1, 2, 3, ...** -/
theorem wazir_walks_in_order : WazirWalksInOrder := by
  intro M hM a ha n
  rw [walk_unique 1 Int.one_pos M hM a ha]
  have e : walk 1 n = w n := by unfold walk; rw [Int.one_mul, Int.one_mul]
  rw [e, spiral_w]

/-- The moves of the Wazir. -/
def wazir : Set (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The moves of the Dabbaba. -/
def dabbaba : Set (ℤ × ℤ) := {(2, 0), (-2, 0), (0, 2), (0, -2)}

/-- The moves of the Alibaba: Dabbaba and Alfil. -/
def alibaba : Set (ℤ × ℤ) := {(2, 0), (-2, 0), (0, 2), (0, -2), (2, 2), (2, -2), (-2, 2), (-2, -2)}

theorem wazir_moves : MovesStraight 1 wazir := by
  refine ⟨by simp [wazir], by simp [wazir], by simp [wazir], by simp [wazir], fun d _ => ?_⟩
  exact ⟨Int.one_dvd _, Int.one_dvd _⟩

theorem dabbaba_moves : MovesStraight 2 dabbaba := by
  refine ⟨by simp [dabbaba], by simp [dabbaba], by simp [dabbaba], by simp [dabbaba], fun d hd => ?_⟩
  simp only [dabbaba, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> decide

theorem alibaba_moves : MovesStraight 2 alibaba := by
  refine ⟨by simp [alibaba], by simp [alibaba], by simp [alibaba], by simp [alibaba], fun d hd => ?_⟩
  simp only [alibaba, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Wazir walk is never trapped, and it is 1, 2, 3, ... (OEIS A000027). -/
theorem wazir_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk wazir a := never_trapped 1 Int.one_pos _ wazir_moves

/-- The Dabbaba walk (OEIS A399158) is never trapped. -/
theorem dabbaba_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk dabbaba a :=
  never_trapped 2 (by decide : (0:ℤ) < 2) _ dabbaba_moves

/-- The Alibaba walk is never trapped. -/
theorem alibaba_never_trapped : ∃ a : ℕ → ℤ × ℤ, IsWalk alibaba a :=
  never_trapped 2 (by decide : (0:ℤ) < 2) _ alibaba_moves

/-- The Dabbaba and the Alibaba make the same walk. -/
theorem alibaba_eq_dabbaba (a b : ℕ → ℤ × ℤ) (ha : IsWalk dabbaba a) (hb : IsWalk alibaba b) :
    a = b :=
  (walk_unique 2 (by decide : (0:ℤ) < 2) _ dabbaba_moves a ha).trans (walk_unique 2 (by decide : (0:ℤ) < 2) _ alibaba_moves b hb).symm

end Straight
