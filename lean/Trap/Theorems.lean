import Trap.Machine

/-!
# The theorems

Their statements are the definitions of `TrapStatement.lean`. The two general ones need no
computation. For a piece, the Lean kernel runs the program of `TrapCheck/Check.lean`
(`decide +kernel`), and `check_sound` turns its answer into the claim.
-/
namespace Trap

open TrapCheck (check natSet)

/-- **Two runs of the same piece agree as far as both go.** -/
theorem runs_agree : RunsAgree := runs_agree'

/-- **A trapped piece has no longer run and no infinite run.** -/
theorem trap_is_the_end : TrapIsTheEnd := trap_is_the_end'

theorem knight_eq : knight = {d | d ∈ TrapCheck.knight} := by
  ext d; simp [knight, TrapCheck.knight]

theorem priest_eq : ferz ∪ knight = {d | d ∈ TrapCheck.priest} := by
  ext d
  simp only [ferz, knight, TrapCheck.priest, TrapCheck.ferz, TrapCheck.knight, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false]

set_option maxRecDepth 100000 in
/-- **The Knight is trapped after 2015 moves on square 2084.** -/
theorem knight_trapped : KnightTrapped := by
  unfold KnightTrapped
  rw [knight_eq]
  exact check_sound _ _ (natSet_lawful 64 32) _ _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The Priest is trapped after 1050 moves on square 858.** -/
theorem priest_trapped : PriestTrapped := by
  unfold PriestTrapped
  rw [priest_eq]
  exact check_sound _ _ (natSet_lawful 64 32) _ _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The Knight's walk begins with the terms that OEIS lists.** -/
theorem knight_begins : KnightBegins := by
  unfold KnightBegins
  rw [knight_eq]
  exact begins_sound _ _ (natSet_lawful 64 32) _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The Priest's walk begins with the terms that OEIS lists.** -/
theorem priest_begins : PriestBegins := by
  unfold PriestBegins
  rw [priest_eq]
  exact begins_sound _ _ (natSet_lawful 64 32) _ _ (by decide +kernel)

end Trap
