import TrapStatement
import Leaper.Main

/-!
# Runs of finitely many moves

No computation here: that runs agree, that a trap is the end, and what a program has to establish
(`Follows`) for a piece to be trapped.
-/
namespace Trap

open Falafel (spiral)
open Straight (IsWalk)

variable {M : Set (ℤ × ℤ)} {L L' : ℕ} {a b : ℕ → ℤ × ℤ}

theorem IsRun.mono (h : IsRun M L a) (hl : L' ≤ L) : IsRun M L' a :=
  ⟨h.start, fun m hm n hn => h.injective m (hm.trans hl) n (hn.trans hl),
   fun n hn => h.move n (lt_of_lt_of_le hn hl), fun n hn => h.lowest n (lt_of_lt_of_le hn hl)⟩

theorem IsRun.fresh (h : IsRun M L a) {n m : ℕ} (hn : n < L) (hm : m ≤ n) : a m ≠ a (n + 1) := by
  intro e
  have := h.injective m (by omega) (n + 1) (by omega) e
  omega

theorem agree_aux (ha : IsRun M L a) (hb : IsRun M L b) : ∀ n, n ≤ L → ∀ m ≤ n, a m = b m := by
  intro n
  induction n with
  | zero =>
    intro _ m hm
    obtain rfl : m = 0 := by omega
    rw [ha.start, hb.start]
  | succ n ih =>
    intro hn m hm
    have ih' := ih (by omega)
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact ih' m (by omega)
    · obtain rfl : m = n + 1 := by omega
      have en : a n = b n := ih' n le_rfl
      have h1 : ¬ spiral (a (n + 1)) < spiral (b (n + 1)) := by
        intro hlt
        obtain ⟨k, hk, e⟩ := hb.lowest n (by omega) (a (n + 1))
          (by rw [← en]; exact ha.move n (by omega)) hlt
        exact ha.fresh (by omega) hk ((ih' k hk).trans e)
      have h2 : ¬ spiral (b (n + 1)) < spiral (a (n + 1)) := by
        intro hlt
        obtain ⟨k, hk, e⟩ := ha.lowest n (by omega) (b (n + 1))
          (by rw [en]; exact hb.move n (by omega)) hlt
        exact hb.fresh (by omega) hk ((ih' k hk).symm.trans e)
      exact Leaper.spiral_inj' _ _ (le_antisymm (not_lt.mp h2) (not_lt.mp h1))

theorem runs_agree' : RunsAgree :=
  fun _ L _ _ ha hb n hn => agree_aux ha hb L le_rfl n hn

theorem trap_is_the_end' : TrapIsTheEnd := by
  rintro M L t ⟨a, ha, -, htrap⟩
  have key : ∀ L' (b : ℕ → ℤ × ℤ), IsRun M L' b → L' ≤ L := by
    intro L' b hb
    by_contra hlt
    have hb' : IsRun M (L + 1) b := hb.mono (by omega)
    have ag := agree_aux ha (hb'.mono (Nat.le_succ L)) L le_rfl
    obtain ⟨m, hm, e⟩ := htrap (b (L + 1)) (by rw [ag L le_rfl]; exact hb'.move L (by omega))
    exact hb'.fresh (Nat.lt_succ_self L) hm ((ag m hm).symm.trans e)
  refine ⟨key, fun ⟨w, hw⟩ => ?_⟩
  have := key (L + 1) w
    ⟨hw.start, fun m _ n _ e => hw.injective e, fun n _ => hw.move n, fun n _ => hw.lowest n⟩
  omega

/-- What the program establishes about the squares `a 0, ..., a L` it goes through. -/
structure Follows (ms : List (ℤ × ℤ)) (L : ℕ) (a : ℕ → ℤ × ℤ) : Prop where
  start : a 0 = (0, 0)
  move : ∀ n < L, a (n + 1) - a n ∈ ms
  fresh : ∀ n < L, ∀ m ≤ n, a m ≠ a (n + 1)
  lowest : ∀ n < L, ∀ q, q - a n ∈ ms → (∀ m ≤ n, a m ≠ q) → spiral (a (n + 1)) ≤ spiral q

theorem Follows.isRun {ms : List (ℤ × ℤ)} (h : Follows ms L a) : IsRun {d | d ∈ ms} L a := by
  refine ⟨h.start, ?_, h.move, ?_⟩
  · intro m hm n hn e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact h.fresh k (by omega) m (by omega) e
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact h.fresh k (by omega) n (by omega) e.symm
  · intro n hn q hq hlt
    by_contra hne
    push Not at hne
    exact absurd (h.lowest n hn q hq hne) (not_le.mpr hlt)

end Trap
