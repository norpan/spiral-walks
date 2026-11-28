import StraightStatement
import Leaper.Spiral

/-!
# Pieces that can move straight

The walk is s times the spiral itself: `nx`, `ny` give the square after (x, y) along the spiral,
and scaling by s keeps the order of the spiral numbers.
-/
namespace Straight

open Falafel (spiral)
open Leaper (rg ps spiral_key spiral_le_of_key spiral_inj max_eq_rg rg_nonneg ps_bounds)

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

/-! ## The next square along the spiral -/

/-- x of the square after (x, y) along the spiral. -/
def nx (x y : ℤ) : ℤ :=
  if x = rg x y ∧ -rg x y < y ∧ y < rg x y then x
  else if y = rg x y ∧ -rg x y < x then x - 1
  else if x = -rg x y ∧ -rg x y < y then x
  else x + 1

/-- y of the square after (x, y) along the spiral. -/
def ny (x y : ℤ) : ℤ :=
  if x = rg x y ∧ -rg x y < y ∧ y < rg x y then y + 1
  else if y = rg x y ∧ -rg x y < x then y
  else if x = -rg x y ∧ -rg x y < y then y - 1
  else y

/-- The next square is one step up, left, down or right. -/
theorem nxt_step (x y : ℤ) :
    (nx x y = x ∧ ny x y = y + 1) ∨ (nx x y = x - 1 ∧ ny x y = y) ∨
    (nx x y = x ∧ ny x y = y - 1) ∨ (nx x y = x + 1 ∧ ny x y = y) := by
  unfold nx ny
  split_ifs <;> simp

/-- The next square has the next position on the ring, or is the first square of the next
ring. -/
theorem nxt_key (x y : ℤ) :
    (rg (nx x y) (ny x y) = rg x y ∧ ps (nx x y) (ny x y) = ps x y + 1) ∨
    (rg (nx x y) (ny x y) = rg x y + 1 ∧ ps x y = 8 * rg x y ∧ ps (nx x y) (ny x y) = 1) := by
  unfold nx ny ps rg
  split_omega

/-- The next square has the next number. -/
theorem spiral_nxt (x y : ℤ) : spiral (nx x y, ny x y) = spiral (x, y) + 1 := by
  rw [spiral_key, spiral_key]
  rcases nxt_key x y with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2]; grind
  · rw [h1, h2, h3]; grind

/-! ## Scaling by s keeps the order -/

theorem rg_scale (s x y : ℤ) (hs : 0 < s) : rg (s * x) (s * y) = s * rg x y := by
  have b := (Falafel.ring_iff x y _).mp (max_eq_rg x y)
  rw [← max_eq_rg, Falafel.ring_iff]
  generalize rg x y = r at b ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := b
  refine ⟨⟨by have := Int.scale_le hs h1; grind, Int.scale_le hs h2⟩,
    ⟨by have := Int.scale_le hs h3; grind, Int.scale_le hs h4⟩, ?_⟩
  rcases h5 with rfl | rfl | rfl | rfl <;> simp [Int.mul_neg]

theorem ps_scale (s x y : ℤ) (hs : 0 < s) : ps (s * x) (s * y) = s * ps x y := by
  unfold ps
  rw [rg_scale s x y hs]
  generalize rg x y = r
  have inj : ∀ a b : ℤ, s * a = s * b ↔ a = b :=
    fun a b => ⟨Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hs), fun h => h ▸ rfl⟩
  have e1 : s * x = s * r ↔ x = r := inj x r
  have e2 : s * y > -(s * r) ↔ y > -r := by
    constructor
    · intro h
      refine Classical.byContradiction fun hc => ?_
      have := Int.scale_le hs (show y ≤ -r by omega); grind
    · intro h
      have := Int.scale_lt hs h; grind
  have e3 : s * y = s * r ↔ y = r := inj y r
  have e4 : s * x = -(s * r) ↔ x = -r := by rw [← Int.mul_neg]; exact inj x (-r)
  simp only [e1, e2, e3, e4]
  split_ifs <;> grind

/-- A lower number stays lower after scaling. -/
theorem scale_lt (s x y x' y' : ℤ) (hs : 0 < s) (h : spiral (x, y) < spiral (x', y')) :
    spiral (s * x, s * y) < spiral (s * x', s * y') := by
  have hkey : rg x y < rg x' y' ∨ (rg x y = rg x' y' ∧ ps x y < ps x' y') := by
    refine Classical.byContradiction fun hc => ?_
    have := spiral_le_of_key x' y' x y (by omega)
    omega
  have hle : spiral (s * x, s * y) ≤ spiral (s * x', s * y') := by
    apply spiral_le_of_key
    rw [rg_scale s x y hs, rg_scale s x' y' hs, ps_scale s x y hs, ps_scale s x' y' hs]
    rcases hkey with h1 | ⟨h1, h2⟩
    · exact Or.inl (Int.scale_lt hs h1)
    · exact Or.inr ⟨by rw [h1], Int.le_of_lt (Int.scale_lt hs h2)⟩
  rcases Int.lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · obtain ⟨e1, e2⟩ := spiral_inj _ _ _ _ heq
    have e1' : x = x' := Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hs) e1
    have e2' : y = y' := Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hs) e2
    rw [e1', e2'] at h
    exact absurd h (Int.lt_irrefl _)

/-! ## The walk -/

/-- One step along the spiral. -/
def step (p : ℤ × ℤ) : ℤ × ℤ := (nx p.1 p.2, ny p.1 p.2)

/-- The spiral itself: the square with number n + 1. -/
def w : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => step (w n)

/-- The walk: the spiral, scaled by s. -/
def walk (s : ℤ) (n : ℕ) : ℤ × ℤ := (s * (w n).1, s * (w n).2)

theorem w_succ (n : ℕ) : w (n + 1) = step (w n) := rfl

theorem spiral_w (n : ℕ) : spiral (w n) = n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [w_succ]
    show spiral (nx (w n).1 (w n).2, ny (w n).1 (w n).2) = ((n + 1 : ℕ) : ℤ) + 1
    rw [spiral_nxt]
    show spiral (w n) + 1 = _
    rw [ih]
    push_cast
    grind

theorem spiral_inj' (p q : ℤ × ℤ) (h : spiral p = spiral q) : p = q := by
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  obtain ⟨a, b⟩ := spiral_inj x y x' y' h
  rw [a, b]

theorem w_injective : Function.Injective w := fun m n h => by
  have h1 := spiral_w m
  have h2 := spiral_w n
  rw [h] at h1
  omega

/-- Every square is on the spiral, at the step given by its number. -/
theorem w_of_spiral (p : ℤ × ℤ) : w (spiral p - 1).toNat = p := by
  apply spiral_inj'
  rw [spiral_w]
  have := Falafel.spiral_pos p.1 p.2
  have e : (p.1, p.2) = p := rfl
  rw [e] at this
  omega

theorem walk_start (s : ℤ) : walk s 0 = (0, 0) := by
  show (s * 0, s * 0) = ((0 : ℤ), (0 : ℤ))
  simp

theorem walk_injective (s : ℤ) (hs : 0 < s) : Function.Injective (walk s) := fun m n h => by
  have h1 : s * (w m).1 = s * (w n).1 := congrArg Prod.fst h
  have h2 : s * (w m).2 = s * (w n).2 := congrArg Prod.snd h
  exact w_injective (Prod.ext (Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hs) h1) (Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hs) h2))

theorem walk_move (s : ℤ) (M : Set (ℤ × ℤ)) (hM : MovesStraight s M) (n : ℕ) :
    walk s (n + 1) - walk s n ∈ M := by
  obtain ⟨m1, m2, m3, m4, -⟩ := hM
  have e : walk s (n + 1) - walk s n
      = (s * nx (w n).1 (w n).2 - s * (w n).1, s * ny (w n).1 (w n).2 - s * (w n).2) := by
    unfold walk
    rw [w_succ]
    rfl
  rw [e]
  rcases nxt_step (w n).1 (w n).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [show (s * (w n).1 - s * (w n).1, s * ((w n).2 + 1) - s * (w n).2) = ((0 : ℤ), s) from
      Prod.ext (by grind) (by grind)]
    exact m3
  · rw [show (s * ((w n).1 - 1) - s * (w n).1, s * (w n).2 - s * (w n).2) = (-s, (0 : ℤ)) from
      Prod.ext (by grind) (by grind)]
    exact m2
  · rw [show (s * (w n).1 - s * (w n).1, s * ((w n).2 - 1) - s * (w n).2) = ((0 : ℤ), -s) from
      Prod.ext (by grind) (by grind)]
    exact m4
  · rw [show (s * ((w n).1 + 1) - s * (w n).1, s * (w n).2 - s * (w n).2) = (s, (0 : ℤ)) from
      Prod.ext (by grind) (by grind)]
    exact m1

theorem walk_lowest (s : ℤ) (hs : 0 < s) (M : Set (ℤ × ℤ)) (hM : MovesStraight s M) (n : ℕ)
    (q : ℤ × ℤ) (hq : q - walk s n ∈ M) (hlt : spiral q < spiral (walk s (n + 1))) :
    ∃ m ≤ n, walk s m = q := by
  obtain ⟨d1, d2⟩ := hM.2.2.2.2 _ hq
  have d1' : s ∣ q.1 := by
    have : q.1 = (q - walk s n).1 + s * (w n).1 := by show q.1 = q.1 - s * (w n).1 + s * (w n).1; grind
    rw [this]
    exact Int.dvd_add d1 (Int.dvd_mul_right s _)
  have d2' : s ∣ q.2 := by
    have : q.2 = (q - walk s n).2 + s * (w n).2 := by show q.2 = q.2 - s * (w n).2 + s * (w n).2; grind
    rw [this]
    exact Int.dvd_add d2 (Int.dvd_mul_right s _)
  obtain ⟨i, hi⟩ := d1'
  obtain ⟨j, hj⟩ := d2'
  have hq' : q = (s * i, s * j) := Prod.ext hi hj
  have hnum : spiral (i, j) < spiral (w (n + 1)) := by
    refine Classical.byContradiction fun hc => ?_
    have hc' : spiral (w (n + 1)) ≤ spiral (i, j) := Int.not_lt.mp hc
    rcases Int.lt_or_eq_of_le hc' with h1 | h1
    · have := scale_lt s (w (n + 1)).1 (w (n + 1)).2 i j hs h1
      rw [hq'] at hlt
      exact absurd hlt (Int.not_lt.mpr (Int.le_of_lt this))
    · have e := spiral_inj' _ _ h1
      rw [hq'] at hlt
      unfold walk at hlt
      rw [e] at hlt
      exact absurd hlt (Int.lt_irrefl _)
  rw [spiral_w] at hnum
  have hpos := Falafel.spiral_pos i j
  refine ⟨(spiral (i, j) - 1).toNat, by push_cast at hnum; omega, ?_⟩
  unfold walk
  rw [w_of_spiral (i, j), hq']

theorem walk_isWalk (s : ℤ) (hs : 0 < s) (M : Set (ℤ × ℤ)) (hM : MovesStraight s M) :
    IsWalk M (walk s) where
  start := walk_start s
  injective := walk_injective s hs
  move := walk_move s M hM
  lowest := walk_lowest s hs M hM

/-- Any sequence that satisfies the definition is this walk. -/
theorem walk_unique (s : ℤ) (hs : 0 < s) (M : Set (ℤ × ℤ)) (hM : MovesStraight s M)
    (a : ℕ → ℤ × ℤ) (ha : IsWalk M a) : a = walk s := by
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
        have han : a n = walk s n := ih n (Nat.le_refl n)
        have hmv : a (n + 1) - walk s n ∈ M := han ▸ ha.move n
        rcases Int.lt_trichotomy (spiral (a (n + 1))) (spiral (walk s (n + 1))) with hlt | heq | hgt
        · obtain ⟨k, hk, hw⟩ := walk_lowest s hs M hM n (a (n + 1)) hmv hlt
          exact absurd ((ih k hk).trans hw) (ha.injective.ne (by omega))
        · exact spiral_inj' _ _ heq
        · have hmv' : walk s (n + 1) - a n ∈ M := han ▸ walk_move s M hM n
          obtain ⟨k, hk, hw⟩ := ha.lowest n (walk s (n + 1)) hmv' hgt
          exact absurd ((ih k hk).symm.trans hw) ((walk_injective s hs).ne (by omega))
  exact funext fun n => main n n (Nat.le_refl n)

/-- The numbers of the walk go up. -/
theorem walk_strictMono (s : ℤ) (hs : 0 < s) : StrictMono (fun n => spiral (walk s n)) := by
  have step : ∀ n, spiral (walk s n) < spiral (walk s (n + 1)) := fun n => by
    apply scale_lt s _ _ _ _ hs
    show spiral (w n) < spiral (w (n + 1))
    rw [spiral_w, spiral_w]
    push_cast
    omega
  intro m n h
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Int.lt_trans (ih h) (step n)
    · exact step m

end Straight
