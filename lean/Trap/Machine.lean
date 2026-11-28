import Trap.Main
import TrapCheck.Check

/-!
# The program is sound

If `TrapCheck.check S ms L t` is true for a lawful store `S`, the piece with the moves `ms` is trapped
after `L` moves on square `t`. Both stores of `TrapCheck/Check.lean` are lawful.
-/
namespace Trap

open Falafel (spiral)
open TrapCheck (VSet sp lowest cands step loop check key inBox natSet arrSet)

theorem sp_eq (p : ℤ × ℤ) : sp p = spiral p := by
  have h : max |p.1| |p.2| = max (max p.1 (-p.1)) (max p.2 (-p.2)) := by abs_omega
  unfold sp spiral
  simp only [h, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- What a store of visited squares has to satisfy, for squares inside its box. -/
structure Lawful {V : Type} (S : VSet V) (wf : V → Prop) : Prop where
  wf_empty : wf S.empty
  wf_ins : ∀ v q, wf v → wf (S.ins v q)
  mem_empty : ∀ q, S.box q = true → S.mem S.empty q = false
  mem_ins : ∀ v q r, wf v → S.box q = true → S.box r = true →
    S.mem (S.ins v q) r = (decide (r = q) || S.mem v r)

theorem lowest_eq_none : ∀ l, lowest l = none → l = []
  | [], _ => rfl
  | q :: l, h => by
    simp only [lowest] at h
    split at h
    · simp at h
    · split at h <;> simp at h

theorem lowest_spec : ∀ (l : List (ℤ × ℤ)) (b : ℤ × ℤ), lowest l = some b →
    b ∈ l ∧ ∀ q ∈ l, sp b ≤ sp q
  | [], b, h => by simp [lowest] at h
  | q :: l, b, h => by
    simp only [lowest] at h
    split at h
    · next hl =>
      have := lowest_eq_none l hl
      subst this
      simp only [Option.some.injEq] at h
      subst h
      simp
    · next c hl =>
      obtain ⟨hc, hmin⟩ := lowest_spec l c hl
      split at h
      · next hlt =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_of_mem _ hc, fun r hr => ?_⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Int.le_of_lt hlt
        · exact hmin r hr
      · next hge =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, fun r hr => ?_⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (by omega)
        · exact Int.le_trans (Int.not_lt.mp hge) (hmin r hr)

theorem mem_cands (ms : List (ℤ × ℤ)) (p q : ℤ × ℤ) : q ∈ cands ms p ↔ q - p ∈ ms := by
  unfold cands
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have : ((p.1 + d.1, p.2 + d.2) : ℤ × ℤ) - p = d := by ext <;> simp <;> omega
    rw [this]
    exact hd
  · intro h
    exact ⟨q - p, h, by ext <;> simp <;> omega⟩

theorem step_spec {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (s s' : V × (ℤ × ℤ))
    (h : step S ms s = some s') :
    (∀ q ∈ cands ms s.2, S.box q = true) ∧ s'.1 = S.ins s.1 s'.2 ∧ s'.2 ∈ cands ms s.2 ∧
    S.mem s.1 s'.2 = false ∧ ∀ q ∈ cands ms s.2, S.mem s.1 q = false → sp s'.2 ≤ sp q := by
  unfold step at h
  simp only at h
  split at h
  · next hbox =>
    split at h
    · simp at h
    · next q hq =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hmem, hmin⟩ := lowest_spec _ _ hq
      rw [List.mem_filter] at hmem
      refine ⟨fun r hr => List.all_eq_true.mp hbox r hr, rfl, hmem.1, by simpa using hmem.2,
        fun r hr hf => hmin r ?_⟩
      rw [List.mem_filter]
      exact ⟨hr, by simp [hf]⟩
  · simp at h

/-- The state after `n` moves, if the program gets that far. -/
def stAt {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (s : V × (ℤ × ℤ)) :
    ℕ → Option (V × (ℤ × ℤ))
  | 0 => some s
  | n + 1 => (stAt S ms s n).bind (step S ms)

theorem stAt_succ' {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (s : V × (ℤ × ℤ)) :
    ∀ n, stAt S ms s (n + 1) = (step S ms s).bind (fun s' => stAt S ms s' n)
  | 0 => by simp [stAt]
  | n + 1 => by
    rw [stAt, stAt_succ' S ms s n]
    cases step S ms s with
    | none => rfl
    | some s' => rfl

theorem loop_eq {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) :
    ∀ n s, loop S ms n s = stAt S ms s n
  | 0, s => rfl
  | n + 1, s => by
    rw [stAt_succ']
    unfold loop
    cases step S ms s with
    | none => rfl
    | some s' => simp [loop_eq S ms n s']

theorem stAt_isSome_mono {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (s0 : V × (ℤ × ℤ)) :
    ∀ n' n, n ≤ n' → (stAt S ms s0 n').isSome → (stAt S ms s0 n).isSome
  | 0, n, hn, h => by
    obtain rfl : n = 0 := by omega
    exact h
  | n' + 1, n, hn, h => by
    rcases Nat.lt_or_ge n (n' + 1) with h1 | h1
    · apply stAt_isSome_mono S ms s0 n' n (by omega)
      rw [stAt] at h
      cases hh : stAt S ms s0 n' with
      | none => rw [hh] at h; simp at h
      | some _ => rfl
    · obtain rfl : n = n' + 1 := by omega
      exact h

/-- The states the program goes through are a run of the walk. -/
theorem state_sound {V : Type} (S : VSet V) (wf : V → Prop) (hS : Lawful S wf)
    (ms : List (ℤ × ℤ)) (L : ℕ) (sL : V × (ℤ × ℤ)) (hbox0 : S.box (0, 0) = true)
    (h : TrapCheck.stateAfter S ms L = some sL) :
    ∃ a : ℕ → ℤ × ℤ, Follows ms L a ∧ a L = sL.2 ∧
      ∀ r, S.box r = true → (S.mem sL.1 r = true ↔ ∃ m ≤ L, a m = r) := by
  unfold TrapCheck.stateAfter at h
  rw [loop_eq] at h
  generalize hs0 : (S.ins S.empty ((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) = s0 at h
  have hL := h
  let a : ℕ → ℤ × ℤ := fun n => ((stAt S ms s0 n).map (·.2)).getD (0, 0)
  have ha0 : a 0 = (0, 0) := by simp [a, stAt, ← hs0]
  have inv : ∀ n ≤ L, ∃ s, stAt S ms s0 n = some s ∧ s.2 = a n ∧ wf s.1 ∧
      (∀ m ≤ n, S.box (a m) = true) ∧
      ∀ r, S.box r = true → (S.mem s.1 r = true ↔ ∃ m ≤ n, a m = r) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨s0, rfl, by rw [ha0, ← hs0], by rw [← hs0]; exact hS.wf_ins _ _ hS.wf_empty,
        ?_, ?_⟩
      · intro m hm
        obtain rfl : m = 0 := by omega
        rw [ha0]; exact hbox0
      · intro r hr
        rw [← hs0]
        show S.mem (S.ins S.empty (0, 0)) r = true ↔ _
        rw [hS.mem_ins _ _ _ hS.wf_empty hbox0 hr, hS.mem_empty r hr]
        simp only [Bool.or_false, decide_eq_true_eq]
        constructor
        · rintro rfl; exact ⟨0, (by omega), ha0⟩
        · rintro ⟨m, hm, rfl⟩
          obtain rfl : m = 0 := by omega
          exact ha0
    | succ n ih =>
      intro hn
      obtain ⟨s, hs, hpos, hwf, hbx, hmem⟩ := ih (by omega)
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp
        (stAt_isSome_mono S ms s0 L (n + 1) hn (by rw [hL]; rfl))
      have hstep : step S ms s = some s' := by
        have := hs'
        rw [stAt, hs] at this
        exact this
      have han : a (n + 1) = s'.2 := by simp [a, hs']
      obtain ⟨hcb, hins, hcand, hfresh, hmin⟩ := step_spec S ms s s' hstep
      have hb' : S.box s'.2 = true := hcb _ hcand
      refine ⟨s', hs', han.symm, by rw [hins]; exact hS.wf_ins _ _ hwf, ?_, ?_⟩
      · intro m hm
        rcases Nat.lt_or_ge m (n + 1) with h1 | h1
        · exact hbx m (by omega)
        · obtain rfl : m = n + 1 := by omega
          rw [han]; exact hb'
      · intro r hr
        rw [hins, hS.mem_ins _ _ _ hwf hb' hr]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (rfl | h1)
          · exact ⟨n + 1, (by omega), han⟩
          · obtain ⟨m, hm, e⟩ := (hmem r hr).mp h1
            exact ⟨m, by omega, e⟩
        · rintro ⟨m, hm, e⟩
          rcases Nat.lt_or_ge m (n + 1) with h1 | h1
          · exact Or.inr ((hmem r hr).mpr ⟨m, by omega, e⟩)
          · obtain rfl : m = n + 1 := by omega
            exact Or.inl (by rw [← e, han])
  have stepf : ∀ n < L, ∃ s s', s.2 = a n ∧
      (∀ r, S.box r = true → (S.mem s.1 r = true ↔ ∃ m ≤ n, a m = r)) ∧
      step S ms s = some s' ∧ s'.2 = a (n + 1) := by
    intro n hn
    obtain ⟨s, hs, hpos, -, -, hmem⟩ := inv n (by omega)
    obtain ⟨s', hs', hpos', -⟩ := inv (n + 1) (by omega)
    refine ⟨s, s', hpos, hmem, ?_, hpos'⟩
    have := hs'
    rw [stAt, hs] at this
    exact this
  have hfol : Follows ms L a := by
    refine ⟨ha0, ?_, ?_, ?_⟩
    · intro n hn
      obtain ⟨s, s', hpos, -, hstep, hpos'⟩ := stepf n hn
      obtain ⟨-, -, hcand, -, -⟩ := step_spec S ms s s' hstep
      rw [hpos, hpos'] at hcand
      exact (mem_cands ms _ _).mp hcand
    · intro n hn m hm e
      obtain ⟨s, s', hpos, hmem, hstep, hpos'⟩ := stepf n hn
      obtain ⟨hcb, -, hcand, hfresh, -⟩ := step_spec S ms s s' hstep
      have := (hmem s'.2 (hcb _ hcand)).mpr ⟨m, hm, by rw [e, hpos']⟩
      rw [hfresh] at this
      exact absurd this (by simp)
    · intro n hn q hq hne
      obtain ⟨s, s', hpos, hmem, hstep, hpos'⟩ := stepf n hn
      obtain ⟨hcb, -, -, -, hmin⟩ := step_spec S ms s s' hstep
      have hqc : q ∈ cands ms s.2 := by rw [hpos]; exact (mem_cands ms _ _).mpr hq
      have hf : S.mem s.1 q = false := by
        cases hc : S.mem s.1 q with
        | false => rfl
        | true =>
          obtain ⟨m, hm, e⟩ := (hmem q (hcb q hqc)).mp hc
          exact absurd e (hne m hm)
      have := hmin q hqc hf
      rw [hpos', sp_eq, sp_eq] at this
      exact this
  obtain ⟨s, hs, hpos, -, -, hmem⟩ := inv L (by omega)
  rw [hL] at hs
  cases hs
  exact ⟨a, hfol, hpos.symm, hmem⟩

theorem loop_succ {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (k : ℕ) (s : V × (ℤ × ℤ)) :
    loop S ms (k + 1) s = (step S ms s).bind (loop S ms k) := by
  cases h : step S ms s <;> simp [loop, h]

/-- A run of `m + n` moves is a run of `m` moves and then one of `n` moves. -/
theorem loop_add {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (n : ℕ) :
    ∀ m s, loop S ms (m + n) s = (loop S ms m s).bind (loop S ms n)
  | 0, s => by rw [Nat.zero_add]; rfl
  | m + 1, s => by
    rw [show m + 1 + n = (m + n) + 1 by omega, loop_succ, loop_succ]
    cases step S ms s with
    | none => rfl
    | some s' => exact loop_add S ms n m s'

theorem stateAfter_add {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (m n : ℕ)
    (s s' : V × (ℤ × ℤ)) (h1 : TrapCheck.stateAfter S ms m = some s) (h2 : loop S ms n s = some s') :
    TrapCheck.stateAfter S ms (m + n) = some s' := by
  unfold TrapCheck.stateAfter at h1 ⊢
  rw [loop_add, h1]
  exact h2

/-- The same check, for a run cut into pieces. -/
theorem check_of_state {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (L : ℕ) (t : ℤ)
    (s : V × (ℤ × ℤ)) (hb : S.box (0, 0) = true) (h1 : TrapCheck.stateAfter S ms L = some s)
    (h2 : TrapCheck.stuck S ms t s = true) : check S ms L t = true := by
  unfold TrapCheck.stateAfter at h1
  unfold check
  rw [h1]
  simp [hb, h2]

/-- **The program is sound.** -/
theorem check_sound {V : Type} (S : VSet V) (wf : V → Prop) (hS : Lawful S wf)
    (ms : List (ℤ × ℤ)) (L : ℕ) (t : ℤ) (h : check S ms L t = true) :
    TrappedAfter {d | d ∈ ms} L t := by
  unfold check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hbox0, h⟩ := h
  cases hL : loop S ms L (S.ins S.empty (0, 0), (0, 0)) with
  | none => rw [hL] at h; simp at h
  | some sL =>
    rw [hL] at h
    simp only [TrapCheck.stuck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨ht, hstuck⟩ := h
    obtain ⟨a, hfol, hpos, hmem⟩ := state_sound S wf hS ms L sL hbox0 hL
    refine ⟨a, hfol.isRun, by rw [hpos, ← sp_eq, ht], fun q hq => ?_⟩
    have hqc : q ∈ cands ms sL.2 := by rw [← hpos]; exact (mem_cands ms _ _).mpr hq
    obtain ⟨hb, hm⟩ := hstuck q hqc
    exact (hmem q hb).mp hm

/-- The walk begins with the numbers of `l`: the test. It runs the program anew for every term. -/
def beginsB {V : Type} (S : VSet V) (ms : List (ℤ × ℤ)) (l : List ℤ) : Bool :=
  S.box (0, 0) && (List.range l.length).all fun n =>
    match TrapCheck.stateAfter S ms n with
    | some s => l[n]? == some (sp s.2)
    | none => false

theorem begins_sound {V : Type} (S : VSet V) (wf : V → Prop) (hS : Lawful S wf)
    (ms : List (ℤ × ℤ)) (l : List ℤ) (h : beginsB S ms l = true) :
    BeginsWith {d | d ∈ ms} l := by
  intro L a ha n hn hlt
  unfold beginsB at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hb, hall⟩ := h
  have hn' := hall n (List.mem_range.mpr hlt)
  cases hs : TrapCheck.stateAfter S ms n with
  | none => rw [hs] at hn'; simp at hn'
  | some s =>
    rw [hs] at hn'
    obtain ⟨a0, hf, hpos, -⟩ := state_sound S wf hS ms n s hb hs
    have e := agree_aux (ha.mono hn) hf.isRun n (by omega) n (by omega)
    rw [e, hpos, ← sp_eq]
    simpa using hn'

/-! ## The two stores are lawful -/

theorem pair_inj {W X Y X' Y' : ℕ} (hY : Y < W) (hY' : Y' < W)
    (h : X * W + Y = X' * W + Y') : X = X' ∧ Y = Y' := by
  have hx : X = X' := by
    rcases Nat.lt_trichotomy X X' with h1 | h1 | h1
    · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h1)
      rw [Nat.succ_mul] at this
      omega
    · exact h1
    · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h1)
      rw [Nat.succ_mul] at this
      omega
  subst hx
  exact ⟨rfl, by omega⟩

theorem key_inj (W K : ℕ) (q r : ℤ × ℤ) (hq : inBox W K q = true) (hr : inBox W K r = true)
    (h : key W K q = key W K r) : r = q := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  simp only [inBox, Bool.and_eq_true, decide_eq_true_eq] at hq hr
  simp only [key] at h
  obtain ⟨e1, e2⟩ := pair_inj (by omega) (by omega) h
  refine Prod.ext ?_ ?_ <;> simp only <;> omega

theorem key_lt (W K : ℕ) (q : ℤ × ℤ) (hq : inBox W K q = true) : key W K q < W * W := by
  obtain ⟨q1, q2⟩ := q
  simp only [inBox, Bool.and_eq_true, decide_eq_true_eq] at hq
  simp only [key]
  have := Nat.mul_le_mul_right W (show (q1 + K).toNat + 1 ≤ W by omega)
  rw [Nat.succ_mul] at this
  omega

theorem natSet_lawful (W K : ℕ) : Lawful (natSet W K) (fun _ => True) where
  wf_empty := trivial
  wf_ins := fun _ _ _ => trivial
  mem_empty := fun q _ => by simp [natSet]
  mem_ins := by
    intro v q r _ hq hr
    show (v ||| 1 <<< key W K q).testBit (key W K r) = (decide (r = q) || v.testBit (key W K r))
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_comm]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e; exact key_inj W K q r hq hr e
    · rintro rfl; rfl

theorem arrSet_lawful (W K : ℕ) : Lawful (arrSet W K) (fun v => v.size = W * W) where
  wf_empty := by simp [arrSet]
  wf_ins := fun v q h => by simpa [arrSet] using h
  mem_empty := fun q _ => by
    show (Array.replicate (W * W) false).getD (key W K q) false = false
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  mem_ins := by
    intro v q r hv hq hr
    show (v.setIfInBounds (key W K q) true).getD (key W K r) false
      = (decide (r = q) || v.getD (key W K r) false)
    have hk := key_lt W K q hq
    by_cases e : key W K q = key W K r
    · have := key_inj W K q r hq hr e
      subst this
      simp [hv, hk]
    · have : r ≠ q := fun h => e (by rw [h])
      simp [e, this]

end Trap
