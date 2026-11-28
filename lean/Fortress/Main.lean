import FortressStatement
import Straight.Main
import Falafel.Numbers

/-!
# The Fortress and the Alfilerzbaba

The walk is every second square of the spiral: `walk n = Straight.w (2 * n)`, the square with
number 2n + 1. Two steps along the spiral are one Dabbaba move or one Ferz move, and a move that
keeps the parity of x + y leads from an odd number to an odd number.
-/
namespace Fortress

open Falafel (spiral spiral_parity)
open Straight (IsWalk nx ny nxt_step spiral_nxt step w w_succ spiral_w spiral_inj' w_injective
  w_of_spiral)

/-- The walk: every second square of the spiral. -/
def walk (n : ℕ) : ℤ × ℤ := w (2 * n)

theorem walk_succ (n : ℕ) : walk (n + 1) = step (step (walk n)) := by
  unfold walk
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by grind, w_succ, w_succ]

theorem spiral_walk (n : ℕ) : spiral (walk n) = 2 * n + 1 := by
  unfold walk
  rw [spiral_w]
  push_cast
  grind

theorem walk_start : walk 0 = (0, 0) := rfl

theorem walk_injective : Function.Injective walk := fun m n h => by
  have := w_injective h
  omega

/-- Two steps along the spiral are a move of the piece. -/
theorem step2_mem (M : Set (ℤ × ℤ)) (hM : MovesLikeFortress M) (p : ℤ × ℤ) :
    step (step p) - p ∈ M := by
  obtain ⟨f1, f2, f3, f4, d1, d2, d3, d4, -⟩ := hM
  obtain ⟨x, y⟩ := p
  have k1 := spiral_nxt x y
  have k2 := spiral_nxt (nx x y) (ny x y)
  have s1 := nxt_step x y
  have s2 := nxt_step (nx x y) (ny x y)
  show (nx (nx x y) (ny x y) - x, ny (nx x y) (ny x y) - y) ∈ M
  generalize nx (nx x y) (ny x y) = c at *
  generalize ny (nx x y) (ny x y) = d at *
  rcases s1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases s2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  first
  | (rw [show (c - x, d - y) = ((1 : ℤ), (1 : ℤ)) from Prod.ext (by omega) (by omega)]; exact f1)
  | (rw [show (c - x, d - y) = ((1 : ℤ), (-1 : ℤ)) from Prod.ext (by omega) (by omega)]; exact f2)
  | (rw [show (c - x, d - y) = ((-1 : ℤ), (1 : ℤ)) from Prod.ext (by omega) (by omega)]; exact f3)
  | (rw [show (c - x, d - y) = ((-1 : ℤ), (-1 : ℤ)) from Prod.ext (by omega) (by omega)]; exact f4)
  | (rw [show (c - x, d - y) = ((2 : ℤ), (0 : ℤ)) from Prod.ext (by omega) (by omega)]; exact d1)
  | (rw [show (c - x, d - y) = ((-2 : ℤ), (0 : ℤ)) from Prod.ext (by omega) (by omega)]; exact d2)
  | (rw [show (c - x, d - y) = ((0 : ℤ), (2 : ℤ)) from Prod.ext (by omega) (by omega)]; exact d3)
  | (rw [show (c - x, d - y) = ((0 : ℤ), (-2 : ℤ)) from Prod.ext (by omega) (by omega)]; exact d4)
  | (rw [show c = x by omega, show d = y by omega] at k2; omega)

theorem walk_move (M : Set (ℤ × ℤ)) (hM : MovesLikeFortress M) (n : ℕ) :
    walk (n + 1) - walk n ∈ M := by
  rw [walk_succ]
  exact step2_mem M hM (walk n)

theorem walk_lowest (M : Set (ℤ × ℤ)) (hM : MovesLikeFortress M) (n : ℕ) (q : ℤ × ℤ)
    (hq : q - walk n ∈ M) (hlt : spiral q < spiral (walk (n + 1))) : ∃ m ≤ n, walk m = q := by
  have hev : (q.1 - (walk n).1 + (q.2 - (walk n).2)) % 2 = 0 :=
    Int.even_iff.mp (hM.2.2.2.2.2.2.2.2 _ hq)
  have p1 := spiral_parity (walk n).1 (walk n).2
  have p2 := spiral_parity q.1 q.2
  rw [show ((walk n).1, (walk n).2) = walk n from rfl, spiral_walk] at p1
  rw [show (q.1, q.2) = q from rfl] at p2
  rw [spiral_walk] at hlt
  have hpos := Falafel.spiral_pos q.1 q.2
  rw [show (q.1, q.2) = q from rfl] at hpos
  push_cast at hlt
  refine ⟨((spiral q - 1) / 2).toNat, by omega, ?_⟩
  unfold walk
  rw [show 2 * ((spiral q - 1) / 2).toNat = (spiral q - 1).toNat by omega]
  exact w_of_spiral q

theorem walk_isWalk (M : Set (ℤ × ℤ)) (hM : MovesLikeFortress M) : IsWalk M walk where
  start := walk_start
  injective := walk_injective
  move := walk_move M hM
  lowest := walk_lowest M hM

/-- Any sequence that satisfies the definition is this walk. -/
theorem walk_unique (M : Set (ℤ × ℤ)) (hM : MovesLikeFortress M) (a : ℕ → ℤ × ℤ)
    (ha : IsWalk M a) : a = walk := by
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
        have hmv : a (n + 1) - walk n ∈ M := han ▸ ha.move n
        rcases Int.lt_trichotomy (spiral (a (n + 1))) (spiral (walk (n + 1))) with hlt | heq | hgt
        · obtain ⟨k, hk, hw⟩ := walk_lowest M hM n (a (n + 1)) hmv hlt
          exact absurd ((ih k hk).trans hw) (ha.injective.ne (by omega))
        · exact spiral_inj' _ _ heq
        · have hmv' : walk (n + 1) - a n ∈ M := han ▸ walk_move M hM n
          obtain ⟨k, hk, hw⟩ := ha.lowest n (walk (n + 1)) hmv' hgt
          exact absurd ((ih k hk).symm.trans hw) (walk_injective.ne (by omega))
  exact funext fun n => main n n (Nat.le_refl n)

end Fortress
