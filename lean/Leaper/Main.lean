import LeaperStatement
import Leaper.Greedy

/-!
# The walk

`w` is the diamond path of the (1, 1)-leaper: the step `nx`, `ny` iterated from the origin.
`walk s` is the same path scaled by s. It satisfies `IsWalk s` for every s > 0, and it is the
only sequence that does.
-/
namespace Leaper

open Falafel (spiral)

/-- One step of the path. -/
def step (P : ℤ × ℤ) : ℤ × ℤ := (nx P.1 P.2, ny P.1 P.2)

/-- The path of the (1, 1)-leaper. -/
def w (n : ℕ) : ℤ × ℤ := step^[n] (0, 0)

/-- The walk of the (s, s)-leaper. -/
def walk (s : ℤ) (n : ℕ) : ℤ × ℤ := (s * (w n).1, s * (w n).2)

theorem w_zero : w 0 = (0, 0) := rfl

theorem w_succ (n : ℕ) : w (n + 1) = step (w n) := Function.iterate_succ_apply' step n (0, 0)

theorem w_par (n : ℕ) : ((w n).1 + (w n).2) % 2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [w_succ]; exact par_next _ _ ih

/-- The path is at the square of rank n after n steps. -/
theorem w_rk (n : ℕ) : rk (w n).1 (w n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [w_succ]
    show rk (nx (w n).1 (w n).2) (ny (w n).1 (w n).2) = ((n + 1 : ℕ) : ℤ)
    rw [rk_next _ _ (w_par n), ih]
    push_cast
    ring

theorem w_injective : Function.Injective w := fun m n h => by
  have h1 := w_rk m
  rw [h, w_rk n] at h1
  exact_mod_cast h1.symm

/-- Every square (p, q) with p + q even is on the path, at step `rk p q`. -/
theorem w_of_rk (p q : ℤ) (h : (p + q) % 2 = 0) : w (rk p q).toNat = (p, q) := by
  have h1 := w_rk (rk p q).toNat
  rw [Int.toNat_of_nonneg (rk_nonneg p q h)] at h1
  obtain ⟨a, b⟩ := rk_inj _ _ p q (w_par _) h h1
  exact Prod.ext a b

theorem walk_start (s : ℤ) : walk s 0 = (0, 0) := by
  simp [walk, w_zero]

theorem walk_succ (s : ℤ) (n : ℕ) :
    walk s (n + 1) = (s * nx (w n).1 (w n).2, s * ny (w n).1 (w n).2) := by
  simp only [walk, w_succ, step]

theorem walk_injective (s : ℤ) (hs : 0 < s) : Function.Injective (walk s) := fun m n h => by
  have h1 : s * (w m).1 = s * (w n).1 := congrArg Prod.fst h
  have h2 : s * (w m).2 = s * (w n).2 := congrArg Prod.snd h
  exact w_injective (Prod.ext (mul_left_cancel₀ hs.ne' h1) (mul_left_cancel₀ hs.ne' h2))

theorem walk_move (s : ℤ) (hs : 0 < s) (n : ℕ) : IsMove s (walk s n) (walk s (n + 1)) := by
  obtain ⟨h1, h2⟩ := next_diag (w n).1 (w n).2
  rw [walk_succ]
  constructor
  · show |s * nx (w n).1 (w n).2 - s * (w n).1| = s
    rcases h1 with h | h <;> rw [h]
    · rw [show s * ((w n).1 + 1) - s * (w n).1 = s by ring]; exact abs_of_pos hs
    · rw [show s * ((w n).1 - 1) - s * (w n).1 = -s by ring, abs_neg]; exact abs_of_pos hs
  · show |s * ny (w n).1 (w n).2 - s * (w n).2| = s
    rcases h2 with h | h <;> rw [h]
    · rw [show s * ((w n).2 + 1) - s * (w n).2 = s by ring]; exact abs_of_pos hs
    · rw [show s * ((w n).2 - 1) - s * (w n).2 = -s by ring, abs_neg]; exact abs_of_pos hs

/-- A coordinate one leap away is s (z ± 1). -/
theorem leap_coord (s z t : ℤ) (hs : 0 < s) (h : |t - s * z| = s) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ t = s * (z + e) := by
  rcases (abs_eq hs.le).mp h with h | h
  · exact ⟨1, Or.inl rfl, by linear_combination h⟩
  · exact ⟨-1, Or.inr rfl, by linear_combination h⟩

theorem walk_lowest (s : ℤ) (hs : 0 < s) (n : ℕ) (q : ℤ × ℤ) (hq : IsMove s (walk s n) q)
    (hlt : spiral q < spiral (walk s (n + 1))) : ∃ m ≤ n, walk s m = q := by
  obtain ⟨e1, he1, hq1⟩ := leap_coord s (w n).1 q.1 hs hq.1
  obtain ⟨e2, he2, hq2⟩ := leap_coord s (w n).2 q.2 hs hq.2
  have hqe : q = (s * ((w n).1 + e1), s * ((w n).2 + e2)) := Prod.ext hq1 hq2
  have hpar := w_par n
  by_cases hb : Before ((w n).1 + e1) ((w n).2 + e2) (w n).1 (w n).2
  · have hpar' : (((w n).1 + e1) + ((w n).2 + e2)) % 2 = 0 := by
      rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> omega
    have hlt' := rk_lt_of_before _ _ _ _ hpar' hpar hb
    rw [w_rk n] at hlt'
    have h0 := rk_nonneg _ _ hpar'
    refine ⟨(rk ((w n).1 + e1) ((w n).2 + e2)).toNat, by omega, ?_⟩
    rw [walk, w_of_rk _ _ hpar', hqe]
  · have := greedy s (w n).1 (w n).2 e1 e2 hs hpar he1 he2 hb
    rw [walk_succ, hqe] at hlt
    exact absurd hlt (not_lt.mpr this)

/-- **The walk of the (s, s)-leaper is a run of the rule.** -/
theorem walk_isWalk (s : ℤ) (hs : 0 < s) : IsWalk s (walk s) where
  start := walk_start s
  injective := walk_injective s hs
  move := walk_move s hs
  lowest := walk_lowest s hs

theorem spiral_inj' (p q : ℤ × ℤ) (h : spiral p = spiral q) : p = q := by
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  obtain ⟨a, b⟩ := spiral_inj x y x' y' h
  rw [a, b]

/-- Any sequence that satisfies the definition is this walk. -/
theorem walk_unique (s : ℤ) (hs : 0 < s) (a : ℕ → ℤ × ℤ) (ha : IsWalk s a) : a = walk s := by
  have main : ∀ n, ∀ m ≤ n, a m = walk s m := by
    intro n
    induction n with
    | zero =>
      intro m hm
      obtain rfl : m = 0 := by omega
      rw [ha.start, walk_start]
    | succ n ih =>
      intro m hm
      by_cases hmn : m ≤ n
      · exact ih m hmn
      · obtain rfl : m = n + 1 := by omega
        have han : a n = walk s n := ih n (le_refl n)
        have hmv : IsMove s (walk s n) (a (n + 1)) := han ▸ ha.move n
        rcases lt_trichotomy (spiral (a (n + 1))) (spiral (walk s (n + 1))) with hlt | heq | hgt
        · obtain ⟨k, hk, hw⟩ := walk_lowest s hs n (a (n + 1)) hmv hlt
          exact absurd ((ih k hk).trans hw) (ha.injective.ne (by omega))
        · exact spiral_inj' _ _ heq
        · have hmv' : IsMove s (a n) (walk s (n + 1)) := han ▸ walk_move s hs n
          obtain ⟨k, hk, hw⟩ := ha.lowest n (walk s (n + 1)) hmv' hgt
          exact absurd ((ih k hk).symm.trans hw) ((walk_injective s hs).ne (by omega))
  exact funext fun n => main n n (le_refl n)

/-- The walk is on (s p, s q) exactly at step `rk p q`. -/
theorem walk_eq_iff (s : ℤ) (hs : 0 < s) (n : ℕ) (p q : ℤ) (h : (p + q) % 2 = 0) :
    walk s n = (s * p, s * q) ↔ (n : ℤ) = rk p q := by
  constructor
  · intro e
    have h1 : s * (w n).1 = s * p := congrArg Prod.fst e
    have h2 : s * (w n).2 = s * q := congrArg Prod.snd e
    rw [← mul_left_cancel₀ hs.ne' h1, ← mul_left_cancel₀ hs.ne' h2, w_rk]
  · intro e
    have h0 := rk_nonneg p q h
    have : n = (rk p q).toNat := by omega
    rw [this, walk, w_of_rk p q h]

end Leaper
