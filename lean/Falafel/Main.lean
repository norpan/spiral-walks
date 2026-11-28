import Statement
import Falafel.Squares
import Falafel.Spiral
import Falafel.Numbers

/-!
# The Falafel walk never ends

The walk is defined by iterating the step of the model. Its stamps (lap, index) go up by one
position at every step, different squares have different stamps, and the greedy rule holds at
every square. From this the walk satisfies `IsWalk` of `Statement.lean`, it is the only sequence
that does, and it visits every square with x + y even.
-/
namespace Falafel

/-! ## The walk and its stamps -/

/-- One step of the walk, in (u, v) coordinates. -/
def step (p : ℤ × ℤ) : ℤ × ℤ := (stepu p.1 p.2, stepv p.1 p.2)

/-- The walk in (u, v) coordinates: the step iterated from the origin. -/
def w : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => step (w n)

/-- The walk in (x, y) coordinates. -/
def walk (n : ℕ) : ℤ × ℤ := ((w n).1 + (w n).2, (w n).1 - (w n).2)

/-- Lap of the n-th square of the walk. -/
def L (n : ℕ) : ℤ := lap (w n).1 (w n).2

/-- Index within its lap of the n-th square of the walk. -/
def J (n : ℕ) : ℤ := idx (w n).1 (w n).2

theorem w_zero : w 0 = (0, 0) := rfl

theorem w_succ (n : ℕ) : w (n + 1) = step (w n) := rfl

theorem L_zero : L 0 = 3 := by decide

theorem J_zero : J 0 = 0 := by decide

/-- Each step goes to the next index of the lap, or from the last index of a lap to the first
index of the next lap. -/
theorem LJ_succ (n : ℕ) :
    (L (n + 1) = L n ∧ J (n + 1) = J n + 1) ∨
    (L (n + 1) = L n + 1 ∧ J (n + 1) = lolap (L n + 1) ∧ J n + 1 = hilap (L n)) := by
  unfold L J
  rw [w_succ]
  exact step_ok (w n).1 (w n).2

theorem LJ_range (n : ℕ) : 3 ≤ L n ∧ lolap (L n) ≤ J n ∧ J n < hilap (L n) :=
  ⟨lap_ge _ _, idx_range _ _⟩

/-- The stamps (lap, index) increase along the walk, in the lexicographic order. -/
theorem LJ_lt {m n : ℕ} (h : m < n) : L m < L n ∨ (L m = L n ∧ J m < J n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hs := LJ_succ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := ih h
      omega
    · omega

theorem w_injective : Function.Injective w := fun m n h => by
  have hL : L m = L n := by unfold L; rw [h]
  have hJ : J m = J n := by unfold J; rw [h]
  rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
  · have := LJ_lt hmn; omega
  · exact hmn
  · have := LJ_lt hmn; omega

/-- Every square whose stamp is not later than that of the n-th square has been visited by
step n. -/
theorem covered (n : ℕ) (u v : ℤ) (h : ¬ (L n < lap u v ∨ (L n = lap u v ∧ J n < idx u v))) :
    ∃ m ≤ n, w m = (u, v) := by
  have hr := idx_range u v
  have hl := lap_ge u v
  induction n with
  | zero =>
    rw [L_zero, J_zero] at h
    have h3 : lap u v = 3 → lolap 3 ≤ idx u v := fun e => e ▸ hr.1
    have h0 : lolap 3 = 0 := by decide
    have e := stamp_inj u v 0 0 (by show lap u v = L 0; rw [L_zero]; omega)
      (by show idx u v = J 0; rw [J_zero]; omega)
    exact ⟨0, Nat.le_refl 0, by rw [w_zero, e.1, e.2]⟩
  | succ k ih =>
    by_cases hk : L k < lap u v ∨ (L k = lap u v ∧ J k < idx u v)
    · have hs := LJ_succ k
      have hhi : L k = lap u v → idx u v < hilap (L k) := fun e => e ▸ hr.2
      have hlo : lap u v = L k + 1 → lolap (L k + 1) ≤ idx u v := fun e => e ▸ hr.1
      have key : lap u v = L (k + 1) ∧ idx u v = J (k + 1) := by omega
      have e := stamp_inj u v (w (k + 1)).1 (w (k + 1)).2 key.1 key.2
      exact ⟨k + 1, Nat.le_refl _, Prod.ext e.1.symm e.2.symm⟩
    · obtain ⟨m, hm, hw⟩ := ih hk
      exact ⟨m, Nat.le_succ_of_le hm, hw⟩

/-! ## From (u, v) back to (x, y) -/

/-- A Falafel move between squares of the form (u + v, u - v) is a rook move in (u, v). -/
theorem isMove_iff_rook (u v u' v' : ℤ) :
    IsMove (u + v, u - v) (u' + v', u' - v') ↔ Rook (u' - u) (v' - v) := by
  simp only [IsMove, Rook]
  abs_omega

/-- A Falafel move from a square of the form (u + v, u - v) leads to a square of that form. -/
theorem rook_of_isMove (u v : ℤ) (q : ℤ × ℤ) (h : IsMove (u + v, u - v) q) :
    ∃ c d, Rook c d ∧ q = (u + c + (v + d), u + c - (v + d)) := by
  obtain ⟨x, y⟩ := q
  simp only [IsMove, Int.abs] at h
  refine ⟨(x + y) / 2 - u, (x - y) / 2 - v, ?_, ?_⟩ <;> simp only [Rook, Prod.mk.injEq] <;> omega

theorem walk_succ (n : ℕ) :
    walk (n + 1) = (stepu (w n).1 (w n).2 + stepv (w n).1 (w n).2,
      stepu (w n).1 (w n).2 - stepv (w n).1 (w n).2) := by
  unfold walk
  rw [w_succ]
  rfl

/-! ## The walk satisfies the definition -/

theorem walk_start : walk 0 = (0, 0) := by decide

theorem walk_injective : Function.Injective walk := fun m n h => by
  have h1 : (w m).1 + (w m).2 = (w n).1 + (w n).2 := congrArg Prod.fst h
  have h2 : (w m).1 - (w m).2 = (w n).1 - (w n).2 := congrArg Prod.snd h
  exact w_injective (Prod.ext (by omega) (by omega))

theorem walk_move (n : ℕ) : IsMove (walk n) (walk (n + 1)) := by
  rw [walk_succ]
  exact (isMove_iff_rook _ _ _ _).mpr (rook_ok (w n).1 (w n).2)

theorem walk_lowest (n : ℕ) (q : ℤ × ℤ) (hq : IsMove (walk n) q)
    (hs : spiral q < spiral (walk (n + 1))) : ∃ m ≤ n, walk m = q := by
  obtain ⟨c, d, hr, rfl⟩ := rook_of_isMove (w n).1 (w n).2 q hq
  rw [walk_succ] at hs
  have hk : ¬ KeyLE (stepu (w n).1 (w n).2) (stepv (w n).1 (w n).2)
      ((w n).1 + c) ((w n).2 + d) :=
    fun hk => absurd hs (Int.not_lt.mpr (spiral_le_of_keyLE _ _ _ _ hk))
  have hl : ¬ (L n < lap ((w n).1 + c) ((w n).2 + d) ∨
      (L n = lap ((w n).1 + c) ((w n).2 + d) ∧ J n < idx ((w n).1 + c) ((w n).2 + d))) :=
    fun hl => hk (greedy _ _ c d hr hl)
  obtain ⟨m, hm, hw⟩ := covered n _ _ hl
  exact ⟨m, hm, by unfold walk; rw [hw]⟩

/-- The walk satisfies the definition in `Statement.lean`. -/
theorem walk_isWalk : IsWalk walk where
  start := walk_start
  injective := walk_injective
  move := walk_move
  lowest := walk_lowest

/-! ## The walk is the only one -/

/-- Any sequence that satisfies the definition is this walk. -/
theorem walk_unique (a : ℕ → ℤ × ℤ) (ha : IsWalk a) : a = walk := by
  have main : ∀ n, ∀ m ≤ n, a m = walk m := by
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
        have han : a n = walk n := ih n (Nat.le_refl n)
        have hmv : IsMove (walk n) (a (n + 1)) := han ▸ ha.move n
        obtain ⟨c, d, -, hq⟩ := rook_of_isMove (w n).1 (w n).2 (a (n + 1)) hmv
        rcases Int.lt_trichotomy (spiral (a (n + 1))) (spiral (walk (n + 1))) with hlt | heq | hgt
        · obtain ⟨k, hk, hw⟩ := walk_lowest n (a (n + 1)) hmv hlt
          exact absurd ((ih k hk).trans hw) (ha.injective.ne (by omega))
        · rw [hq, walk_succ] at heq ⊢
          obtain ⟨e1, e2⟩ := spiral_uv_inj _ _ _ _ heq
          rw [e1, e2]
        · have hmv' : IsMove (a n) (walk (n + 1)) := han ▸ walk_move n
          obtain ⟨k, hk, hw⟩ := ha.lowest n (walk (n + 1)) hmv' hgt
          exact absurd ((ih k hk).symm.trans hw) (walk_injective.ne (by omega))
  exact funext fun n => main n n (Nat.le_refl n)

/-! ## The walk visits every square of its colour -/

/-- From the first index of a lap the walk runs through the lap in order. -/
theorem run_lap (n : ℕ) (hJ : J n = lolap (L n)) (j : ℕ) (hj : lolap (L n) + j < hilap (L n)) :
    L (n + j) = L n ∧ J (n + j) = lolap (L n) + j := by
  induction j with
  | zero => exact ⟨rfl, by simpa using hJ⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by push_cast at hj ⊢; omega)
    have hs := LJ_succ (n + j)
    rw [h1] at hs
    show L (n + j + 1) = L n ∧ J (n + j + 1) = lolap (L n) + ((j + 1 : ℕ) : ℤ)
    push_cast at hj ⊢
    omega

/-- The walk reaches the first index of every lap. -/
theorem reach_lap (k : ℕ) : ∃ n, L n = 3 + k ∧ J n = lolap (L n) := by
  induction k with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ k ih =>
    obtain ⟨n, hL, hJ⟩ := ih
    have hr0 := LJ_range n
    have hc : ((hilap (L n) - 1 - lolap (L n)).toNat : ℤ) = hilap (L n) - 1 - lolap (L n) :=
      Int.toNat_of_nonneg (by omega)
    obtain ⟨h1, h2⟩ := run_lap n hJ (hilap (L n) - 1 - lolap (L n)).toNat (by omega)
    have hs := LJ_succ (n + (hilap (L n) - 1 - lolap (L n)).toNat)
    have hr := LJ_range (n + (hilap (L n) - 1 - lolap (L n)).toNat + 1)
    refine ⟨n + (hilap (L n) - 1 - lolap (L n)).toNat + 1, ?_⟩
    rcases hs with ⟨e1, e2⟩ | ⟨e1, e2, -⟩
    · rw [e1, h1] at hr
      omega
    · rw [h1] at e1 e2
      rw [e1]
      exact ⟨by push_cast; omega, e2⟩

/-- The walk visits every square (u, v). -/
theorem w_surjective : Function.Surjective w := by
  rintro ⟨u, v⟩
  have hl := lap_ge u v
  have hr := idx_range u v
  obtain ⟨n, hL, hJ⟩ := reach_lap (lap u v - 3).toNat
  have hL' : L n = lap u v := by omega
  rw [← hL'] at hr
  have hc : ((idx u v - lolap (L n)).toNat : ℤ) = idx u v - lolap (L n) :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨h1, h2⟩ := run_lap n hJ (idx u v - lolap (L n)).toNat (by omega)
  have e := stamp_inj (w (n + (idx u v - lolap (L n)).toNat)).1
    (w (n + (idx u v - lolap (L n)).toNat)).2 u v (h1.trans hL') (by
      show J (n + (idx u v - lolap (L n)).toNat) = idx u v
      omega)
  exact ⟨_, Prod.ext e.1 e.2⟩

/-- Every lap R ≥ 4 starts at some step n. From there the walk visits, in order, squares with
lap number R and indices lo R, ..., hi R - 1. -/
theorem lap_run (R : ℤ) (hR : 4 ≤ R) :
    ∃ n, ∀ j : ℕ, lo R + j < hi R →
      lapnum (w (n + j)).1 (w (n + j)).2 = R ∧ pos (w (n + j)).1 (w (n + j)).2 = lo R + j := by
  obtain ⟨n, hL, hJ⟩ := reach_lap (R - 3).toNat
  have hLR : L n = R := by omega
  have h3 : ¬ R ≤ 3 := by omega
  refine ⟨n, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := run_lap n hJ j (by rw [hLR, lolap_big h3, hilap_big h3]; exact hj)
  rw [hLR] at h1
  rw [hLR, lolap_big h3] at h2
  have hbig : ¬ lapnum (w (n + j)).1 (w (n + j)).2 ≤ 3 := fun hlow => by
    have h4 : L (n + j) = 3 := lap_low hlow
    omega
  exact ⟨by rw [← lap_big hbig]; exact h1, by rw [← idx_big hbig]; exact h2⟩

/-- **The walk follows the closed-form path.** Every lap R ≥ 4 starts at some step n, and from
there the walk runs through the squares `(squ R j, sqv R j)` for j = lo R, ..., hi R - 1 in order. -/
theorem walk_follows_path (R : ℤ) (hR : 4 ≤ R) :
    ∃ n, ∀ j : ℕ, lo R + j < hi R → w (n + j) = (squ R (lo R + j), sqv R (lo R + j)) := by
  obtain ⟨n, hn⟩ := lap_run R hR
  refine ⟨n, fun j hj => ?_⟩
  obtain ⟨e1, e2⟩ := hn j hj
  have hs := sq_pos (w (n + j)).1 (w (n + j)).2 (by omega)
  rw [e1, e2] at hs
  exact Prod.ext hs.1.symm hs.2.symm

/-- **Exact cover.** For R ≥ 4, the squares with lap number R are exactly the squares of the
closed-form path of lap R. -/
theorem lapnum_eq_iff (R : ℤ) (hR : 4 ≤ R) (u v : ℤ) :
    lapnum u v = R ↔ ∃ j, lo R ≤ j ∧ j < hi R ∧ squ R j = u ∧ sqv R j = v := by
  constructor
  · rintro rfl
    exact ⟨pos u v, (pos_range u v hR).1, (pos_range u v hR).2, (sq_pos u v hR).1,
      (sq_pos u v hR).2⟩
  · rintro ⟨j, h1, h2, rfl, rfl⟩
    obtain ⟨n, hn⟩ := lap_run R hR
    obtain ⟨m, hm⟩ := walk_follows_path R hR
    have hc : ((j - lo R).toNat : ℤ) = j - lo R := Int.toNat_of_nonneg (by omega)
    have e1 := (hn (j - lo R).toNat (by omega)).1
    have e2 := (hn (j - lo R).toNat (by omega)).2
    have hs := sq_pos (w (n + (j - lo R).toNat)).1 (w (n + (j - lo R).toNat)).2 (by omega)
    rw [e1, e2, hc] at hs
    have hj : lo R + (j - lo R) = j := by omega
    rw [hj] at hs
    rw [hs.1, hs.2]
    exact e1

/-- The first 80 squares of the walk are the squares of the table. -/
theorem first_eighty (n : ℕ) (h : n < 80) : w n = pget n := by
  have h0 : J 0 = lolap (L 0) := by decide
  have hh : hilap (L 0) = 80 := by decide
  have hl : lolap (L 0) = 0 := by decide
  obtain ⟨h1, h2⟩ := run_lap 0 h0 n (by rw [hh, hl]; omega)
  rw [Nat.zero_add] at h1 h2
  rw [L_zero] at h1
  rw [hl] at h2
  have hlow : lapnum (w n).1 (w n).2 ≤ 3 := by
    refine Classical.byContradiction fun hbig => ?_
    have h4 : L n = lapnum (w n).1 (w n).2 := lap_big hbig
    omega
  have hi' : J n = (pidx (w n).1 (w n).2 : ℤ) := idx_low hlow
  have hp : pidx (w n).1 (w n).2 = n := by omega
  have hm := (prefix_mem (w n).1 (w n).2 hlow).2
  rw [hp] at hm
  exact hm.symm

/-- A square has lap number at most 3 exactly if it is one of the first 80 squares of the walk. -/
theorem lapnum_le_three_iff (u v : ℤ) : lapnum u v ≤ 3 ↔ ∃ n < 80, w n = (u, v) := by
  constructor
  · intro h
    obtain ⟨hi, hg⟩ := prefix_mem u v h
    exact ⟨pidx u v, hi, (first_eighty _ hi).trans hg⟩
  · rintro ⟨n, hn, hw⟩
    have h1 := (prefix_table n hn).1
    rw [← first_eighty n hn, hw] at h1
    exact h1

/-- The walk visits every square (x, y) with x + y even. -/
theorem walk_visits (x y : ℤ) (h : Even (x + y)) : ∃ n, walk n = (x, y) := by
  rw [Int.even_iff] at h
  obtain ⟨n, hn⟩ := w_surjective ((x + y) / 2, (x - y) / 2)
  refine ⟨n, ?_⟩
  unfold walk
  rw [hn, Prod.mk.injEq]
  constructor <;> omega

/-- Every square of the walk has x + y even. -/
theorem walk_even (n : ℕ) : Even ((walk n).1 + (walk n).2) :=
  ⟨(w n).1, by simp only [walk]; omega⟩

/-! ## The terms are the odd positive integers, each once -/

/-- Every term of the walk is odd. -/
theorem walk_term_odd (n : ℕ) : Odd (spiral (walk n)) := by
  rw [Int.odd_iff]
  have h := spiral_parity ((w n).1 + (w n).2) ((w n).1 - (w n).2)
  unfold walk
  omega

/-- No number is the spiral number of two steps of the walk. -/
theorem walk_term_injective : Function.Injective (fun n => spiral (walk n)) := fun m n h => by
  have e := spiral_uv_inj (w m).1 (w m).2 (w n).1 (w n).2 h
  exact w_injective (Prod.ext e.1 e.2)

/-- Every odd positive integer is the spiral number of exactly one step of the walk. -/
theorem walk_term_unique (k : ℤ) (hk : 0 < k) (hodd : Odd k) : ∃! n, spiral (walk n) = k := by
  obtain ⟨⟨x, y⟩, hp⟩ := spiral_surjective k hk
  have hpar := spiral_parity x y
  rw [hp] at hpar
  rw [Int.odd_iff] at hodd
  obtain ⟨n, hn⟩ := walk_visits x y (Int.even_iff.mpr (by omega))
  have hk' : spiral (walk n) = k := by rw [hn, hp]
  exact ⟨n, hk', fun m hm => walk_term_injective (hm.trans hk'.symm)⟩

end Falafel
