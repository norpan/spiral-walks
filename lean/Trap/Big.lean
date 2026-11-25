import Trap.Theorems

/-!
# The two long walks

Carpenter and Leopard take 2.5x10^8 moves each, too many for the Lean kernel. Here the program
of `TrapCheck/Check.lean` is run as compiled code (`native_decide`). That adds the axiom
`Lean.ofReduceBool` (and `Lean.trustCompiler`): one has to trust the Lean compiler for the
run itself. That the program's answer gives the claim is `check_sound`, proved in the kernel.
-/
namespace Trap

open TrapCheck (check arrSet natSet)

theorem carpenter_eq : dabbaba ∪ knight = {d | d ∈ TrapCheck.carpenter} := by
  ext d
  simp only [dabbaba, knight, TrapCheck.carpenter, TrapCheck.dabbaba, TrapCheck.knight, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]

theorem carpenter_check : check (arrSet 16801 8400) TrapCheck.carpenter 253925075 259115490 = true := by
  native_decide

/-- **The Carpenter is trapped after 253,925,075 moves on square 259,115,490.** -/
theorem carpenter_trapped : CarpenterTrapped := by
  unfold CarpenterTrapped
  rw [carpenter_eq]
  exact check_sound _ _ (arrSet_lawful 16801 8400) _ _ _ carpenter_check

theorem leopard_eq : ferz ∪ alfil ∪ knight = {d | d ∈ TrapCheck.leopard} := by
  ext d
  simp only [ferz, alfil, knight, TrapCheck.leopard, TrapCheck.ferz, TrapCheck.alfil, TrapCheck.knight, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

theorem leopard_check : check (arrSet 16801 8400) TrapCheck.leopard 256730881 267545105 = true := by
  native_decide

/-- **The Leopard is trapped after 256,730,881 moves on square 267,545,105.** -/
theorem leopard_trapped : LeopardTrapped := by
  unfold LeopardTrapped
  rw [leopard_eq]
  exact check_sound _ _ (arrSet_lawful 16801 8400) _ _ _ leopard_check

set_option maxRecDepth 100000 in
/-- **The Carpenter's walk begins with the terms that OEIS lists.** -/
theorem carpenter_begins : CarpenterBegins := by
  unfold CarpenterBegins
  rw [carpenter_eq]
  exact begins_sound _ _ (natSet_lawful 64 32) _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The Leopard's walk begins with the terms that OEIS lists.** -/
theorem leopard_begins : LeopardBegins := by
  unfold LeopardBegins
  rw [leopard_eq]
  exact begins_sound _ _ (natSet_lawful 64 32) _ _ (by decide +kernel)

end Trap
