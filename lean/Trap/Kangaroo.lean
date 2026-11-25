import Trap.Theorems
import Trap.KangarooData

/-!
# The Kangaroo

Its 59,676 moves are too many for the Lean kernel in one piece (about 2 GB of memory per 1000
moves). So the run is cut into 12 pieces. `Trap/KangarooData.lean` holds the state of the program
after each piece, as generated numbers; the kernel checks every piece (`decide +kernel`) and the
pieces are joined by `stateAfter_add`. A wrong number in the data file would make a piece fail.
-/
namespace Trap

open TrapCheck (loop natSet stateAfter stuck)

theorem kangaroo_eq : alfil ∪ knight = {d | d ∈ TrapCheck.kangaroo} := by
  ext d
  simp only [alfil, knight, TrapCheck.kangaroo, TrapCheck.alfil, TrapCheck.knight, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem kpart1 : stateAfter (natSet 340 170) TrapCheck.kangaroo 5000 = some kst1 := by decide +kernel

theorem kpart2 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst1 = some kst2 := by
  decide +kernel

theorem kpart3 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst2 = some kst3 := by
  decide +kernel

theorem kpart4 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst3 = some kst4 := by
  decide +kernel

theorem kpart5 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst4 = some kst5 := by
  decide +kernel

theorem kpart6 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst5 = some kst6 := by
  decide +kernel

theorem kpart7 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst6 = some kst7 := by
  decide +kernel

theorem kpart8 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst7 = some kst8 := by
  decide +kernel

theorem kpart9 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst8 = some kst9 := by
  decide +kernel

theorem kpart10 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst9 = some kst10 := by
  decide +kernel

theorem kpart11 : loop (natSet 340 170) TrapCheck.kangaroo 5000 kst10 = some kst11 := by
  decide +kernel

theorem kpart12 : loop (natSet 340 170) TrapCheck.kangaroo 4676 kst11 = some kst12 := by
  decide +kernel

theorem kstuck : stuck (natSet 340 170) TrapCheck.kangaroo 57552 kst12 = true := by decide +kernel

theorem kstate2 : stateAfter (natSet 340 170) TrapCheck.kangaroo 10000 = some kst2 :=
  stateAfter_add _ _ 5000 5000 _ _ kpart1 kpart2

theorem kstate3 : stateAfter (natSet 340 170) TrapCheck.kangaroo 15000 = some kst3 :=
  stateAfter_add _ _ 10000 5000 _ _ kstate2 kpart3

theorem kstate4 : stateAfter (natSet 340 170) TrapCheck.kangaroo 20000 = some kst4 :=
  stateAfter_add _ _ 15000 5000 _ _ kstate3 kpart4

theorem kstate5 : stateAfter (natSet 340 170) TrapCheck.kangaroo 25000 = some kst5 :=
  stateAfter_add _ _ 20000 5000 _ _ kstate4 kpart5

theorem kstate6 : stateAfter (natSet 340 170) TrapCheck.kangaroo 30000 = some kst6 :=
  stateAfter_add _ _ 25000 5000 _ _ kstate5 kpart6

theorem kstate7 : stateAfter (natSet 340 170) TrapCheck.kangaroo 35000 = some kst7 :=
  stateAfter_add _ _ 30000 5000 _ _ kstate6 kpart7

theorem kstate8 : stateAfter (natSet 340 170) TrapCheck.kangaroo 40000 = some kst8 :=
  stateAfter_add _ _ 35000 5000 _ _ kstate7 kpart8

theorem kstate9 : stateAfter (natSet 340 170) TrapCheck.kangaroo 45000 = some kst9 :=
  stateAfter_add _ _ 40000 5000 _ _ kstate8 kpart9

theorem kstate10 : stateAfter (natSet 340 170) TrapCheck.kangaroo 50000 = some kst10 :=
  stateAfter_add _ _ 45000 5000 _ _ kstate9 kpart10

theorem kstate11 : stateAfter (natSet 340 170) TrapCheck.kangaroo 55000 = some kst11 :=
  stateAfter_add _ _ 50000 5000 _ _ kstate10 kpart11

theorem kstate12 : stateAfter (natSet 340 170) TrapCheck.kangaroo 59676 = some kst12 :=
  stateAfter_add _ _ 55000 4676 _ _ kstate11 kpart12

/-- **The Kangaroo is trapped after 59,676 moves on square 57,552.** -/
theorem kangaroo_trapped : KangarooTrapped := by
  unfold KangarooTrapped
  rw [kangaroo_eq]
  exact check_sound _ _ (natSet_lawful 340 170) _ _ _
    (check_of_state _ _ _ _ _ (by decide) kstate12 kstuck)

set_option maxRecDepth 100000 in
/-- **The Kangaroo's walk begins with the terms that OEIS lists.** -/
theorem kangaroo_begins : KangarooBegins := by
  unfold KangarooBegins
  rw [kangaroo_eq]
  exact begins_sound _ _ (natSet_lawful 64 32) _ _ (by decide +kernel)

end Trap
