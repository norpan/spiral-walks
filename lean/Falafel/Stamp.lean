import Falafel.Model

/-!
# Time stamps for every square

`lap u v` and `idx u v` say when the walk visits (u, v): in which lap, and at which index within
the lap. Lap 3 stands for the first 80 squares, which are kept as a table. `stepu`, `stepv` give
the next square. Nothing here is trusted.
-/
namespace Falafel

/-- The first 80 squares of the walk, in (u, v), taken from a simulation of the walk.
`Prefix.lean` checks every one of them, so the table is not trusted. -/
def prefixList : List (ℤ × ℤ) :=
  [(0, 0), (1, 0), (-1, 0), (-1, -1), (0, -1), (0, 1), (1, 1), (1, -1), (2, -1), (2, 0), (2, 1),
   (2, 2), (0, 2), (1, 2), (-1, 2), (-1, 1), (-2, 1), (-2, 0), (-2, -1), (-2, -2), (0, -2), (1,
   -2), (-1, -2), (-1, -3), (0, -3), (1, -3), (2, -3), (2, -2), (3, -2), (3, 0), (3, 1), (3,
   -1), (4, -1), (4, 0), (4, 1), (4, 2), (3, 2), (3, 3), (1, 3), (0, 3), (-1, 3), (-2, 3), (-2,
   2), (-3, 2), (-3, 0), (-3, -1), (-3, 1), (-4, 1), (-4, 0), (-4, -1), (-4, -2), (-3, -2), (-3,
   -3), (-2, -3), (-2, -4), (0, -4), (1, -4), (-1, -4), (-1, -5), (0, -5), (1, -5), (2, -5), (2,
   -4), (3, -4), (3, -3), (4, -3), (4, -2), (5, -2), (5, 0), (5, 1), (5, -1), (6, -1), (6, 0),
   (6, 1), (6, 2), (5, 2), (5, 3), (4, 3), (2, 3), (2, 4)]

/-- Index of (u, v) among the first 80 squares; 80 if it is not one of them. -/
def pidx (u v : ℤ) : ℕ := prefixList.idxOf (u, v)

/-- The i-th of the first 80 squares. -/
def pget (i : ℕ) : ℤ × ℤ := prefixList.getD i (0, 0)

/-- Lap of (u, v): 3 for the first 80 squares, else the lap number. -/
def lap (u v : ℤ) : ℤ := if lapnum u v ≤ 3 then 3 else lapnum u v

/-- Index of (u, v) within its lap. -/
def idx (u v : ℤ) : ℤ := if lapnum u v ≤ 3 then (pidx u v : ℤ) else pos u v

/-- First index of lap R. -/
def lolap (R : ℤ) : ℤ := if R ≤ 3 then 0 else lo R

/-- One more than the last index of lap R. -/
def hilap (R : ℤ) : ℤ := if R ≤ 3 then 80 else hi R

/-- First coordinate of the square after (u, v). -/
def stepu (u v : ℤ) : ℤ :=
  if lapnum u v ≤ 3 ∧ pidx u v < 79 then (pget (pidx u v + 1)).1 else u + du u v

/-- Second coordinate of the square after (u, v). -/
def stepv (u v : ℤ) : ℤ :=
  if lapnum u v ≤ 3 ∧ pidx u v < 79 then (pget (pidx u v + 1)).2 else v + dv u v

/-- (u', v') is visited later than (u, v). -/
abbrev Later (u' v' u v : ℤ) : Prop :=
  lap u v < lap u' v' ∨ (lap u v = lap u' v' ∧ idx u v < idx u' v')

/-- The spiral number of (a, b) is at most that of (c, d), in terms of ring and position. -/
abbrev KeyLE (a b c d : ℤ) : Prop :=
  ring a b < ring c d ∨ (ring a b = ring c d ∧ rpos a b ≤ rpos c d)

/-- (a, b) is a Falafel move in (u, v) coordinates: a rook move of 1 or 2 squares. -/
abbrev Rook (a b : ℤ) : Prop :=
  (b = 0 ∧ (a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2)) ∨ (a = 0 ∧ (b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2))

end Falafel
