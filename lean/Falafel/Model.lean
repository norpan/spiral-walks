import Statement

/-!
# The model of the walk, in (u, v) coordinates

With u = (x + y)/2 and v = (x - y)/2 the Falafel moves like a rook limited to 1 or 2 squares.
Every square (u, v) gets a lap number `lapnum`, an index `pos` within its lap, and a move
`(du, dv)`. Lap R ≥ 4 has the indices `lo R` to `hi R - 1`. Squares with lap number at most 3
are the irregular first 80 squares, which are kept as a table in `Stamp.lean`.

Nothing in this file is trusted: the theorems proved from it are about the definitions in
`Statement.lean`. The definitions are written with plain integer arithmetic and `if`, so that
`omega` and `decide` can work with them. `py/leanmodel.py` reads them from this file and
`py/test_lemmas.py` tests them against a simulation of the walk.
-/
namespace Falafel

/-- Lap number of the square (u, v), 0 on the centre block. The ten regions are numbered as in
the write-up. Squares with lap number at most 3 are the first 80 squares of the walk. -/
def lapnum (u v : ℤ) : ℤ :=
  if v ≥ 2 then
    if u ≤ 1 then
      if u + v ≥ 1 then v                               -- 1 north row
      else (v - u) / 2 + 1                              -- 2 north-west staircase
    else if u - 3 * v ≥ -6 then (u + v - 1) / 2         -- 8 north-east staircase
    else if u = 3 then 2 * (v / 2) + 1                  -- 9 column 3
    else if (u + 3 * v) % 6 ≤ 2 then                    -- 10 descent
      if (u + 3 * v) % 6 ≤ 0 then 2 * ((u + 3 * v) / 6) - 2
      else 2 * ((u + 3 * v) / 6) - 1
    else
      if (u + 3 * v) % 6 ≤ 4 then 2 * ((u + 3 * v) / 6)
      else 2 * ((u + 3 * v) / 6) + 1
  else if v ≤ -2 then
    if u ≤ -2 then (1 - u - v) / 2                      -- 4 south-west staircase
    else if u ≤ 1 then (2 - v) / 2                      -- 5 south corner
    else (u - v) / 2                                    -- 6 south-east staircase
  else if u ≤ -2 then (3 - u) / 2                       -- 3 west corner
  else if u ≥ 2 then (u + 1) / 2                        -- 7 east corner
  else 0

/-- First index of lap R, for R ≥ 4. Indices are counted from the start of the north-west
staircase, so the squares of the north row have negative indices. -/
def lo (R : ℤ) : ℤ := -(R + 1 + 2 * (R % 2))

/-- One more than the last index of lap R, for R ≥ 4. -/
def hi (R : ℤ) : ℤ := 11 * R + 3 + (3 * R - 10 + 5 * (R % 2)) / 2

/-- Index of (u, v) within lap R, when R is its lap number and R ≥ 4. -/
def posIn (R u v : ℤ) : ℤ :=
  if v ≥ 2 then
    if u ≤ 1 then
      if u + v ≥ 1 then
        if v % 2 = 0 then (if u ≤ -1 then -u - v else if u ≤ 0 then -v - 1 else -v) else -u - v
      else 2 * (R - 1 - v) + (v - u) % 2
    else if u - 3 * v ≥ -6 then 10 * R + 2 + (2 * R - u + v - 1) - 1
    else if u = 3 then (if v % 2 = 0 then -v - 4 else -v - 2)
    else if (u + 3 * v) % 6 ≤ 1 then 11 * R + 3 * v - 3 * ((u + 3 * v) / 6) - 1
    else if (u + 3 * v) % 6 ≤ 3 then 11 * R + 3 * v - 3 * ((u + 3 * v) / 6) - 2
    else 11 * R + 3 * v - 3 * ((u + 3 * v) / 6) - 3
  else if v ≤ -2 then
    if u ≤ -2 then 2 * R + 2 + (u - v + 2 * R - 3) - 1
    else if u ≤ 1 then
      if v % 2 = 0 then 6 * R - 5 + (if u ≤ -1 then 2 else u)
      else 6 * R - 5 + 4 + u
    else 6 * R + 1 + (u + v + 2 * R - 2) - 1
  else if u ≤ -2 then
    if u % 2 = 0 then 2 * R - 4 + 4 - v
    else 2 * R - 4 + (if v ≤ -1 then 1 else if v ≤ 0 then 0 else 2)
  else if u ≥ 2 then
    if u % 2 = 0 then 10 * R - 4 + 4 + v
    else 10 * R - 4 + (if v ≤ -1 then 2 else v)
  else 0

/-- Index of (u, v) within its lap, for squares with lap number at least 4. -/
def pos (u v : ℤ) : ℤ := posIn (lapnum u v) u v

/-- First coordinate of the move made from (u, v). -/
def du (u v : ℤ) : ℤ :=
  if v ≥ 2 then
    if u ≤ 1 then
      if u + v ≥ 1 then
        if u + v ≤ 1 then 0
        else if v % 2 = 0 then (if u ≤ -1 then -1 else if u ≤ 0 then 1 else -2) else -1
      else if (v - u) % 2 = 0 then -1 else 0
    else if u - 3 * v ≥ -6 then
      if u - 3 * v ≤ -5 then -2 else if (u + v) % 2 = 0 then -1 else 0
    else if u = 3 then (if v % 2 = 0 then 0 else -2)
    else if (u + 3 * v) % 6 ≤ 2 then
      if (u + 3 * v) % 6 ≤ 0 then -2
      else if (u + 3 * v) % 6 ≤ 1 then -2
      else (if u ≤ 2 then -2 else -1)
    else
      if (u + 3 * v) % 6 ≤ 3 then 0
      else if (u + 3 * v) % 6 ≤ 4 then -1
      else 0
  else if v ≤ -2 then
    if u ≤ -2 then
      if (u + v) % 2 = 0 then (if u ≥ -2 then 2 else 1) else 0
    else if u ≤ 1 then
      if v % 2 = 0 then (if u ≤ -1 then 0 else if u ≤ 0 then 1 else -2) else 1
    else if (u - v) % 2 = 0 then 1 else 0
  else if u ≤ -2 then
    if u % 2 = 0 then 0 else (if v ≤ 0 then 0 else -1)
  else if u ≥ 2 then
    if u % 2 = 0 then 0 else (if v ≤ -1 then 1 else 0)
  else 0

/-- Second coordinate of the move made from (u, v). -/
def dv (u v : ℤ) : ℤ :=
  if v ≥ 2 then
    if u ≤ 1 then
      if u + v ≥ 1 then
        if u + v ≤ 1 then -1
        else if v % 2 = 0 then (if u ≤ -1 then 0 else if u ≤ 0 then 0 else 0) else 0
      else if (v - u) % 2 = 0 then 0 else (if v ≤ 2 then -2 else -1)
    else if u - 3 * v ≥ -6 then
      if u - 3 * v ≤ -5 then 0 else if (u + v) % 2 = 0 then 0 else 1
    else if u = 3 then (if v % 2 = 0 then 1 else 0)
    else if (u + 3 * v) % 6 ≤ 2 then
      if (u + 3 * v) % 6 ≤ 0 then 0
      else if (u + 3 * v) % 6 ≤ 1 then 0
      else (if u ≤ 2 then 0 else 0)
    else
      if (u + 3 * v) % 6 ≤ 3 then 1
      else if (u + 3 * v) % 6 ≤ 4 then 0
      else 1
  else if v ≤ -2 then
    if u ≤ -2 then
      if (u + v) % 2 = 0 then (if u ≥ -2 then 0 else 0) else -1
    else if u ≤ 1 then
      if v % 2 = 0 then (if u ≤ -1 then -1 else if u ≤ 0 then 0 else 0) else 0
    else if (u - v) % 2 = 0 then 0 else (if v ≥ -2 then 2 else 1)
  else if u ≤ -2 then
    if u % 2 = 0 then -1 else (if v ≤ -1 then 2 else if v ≤ 0 then -1 else 0)
  else if u ≥ 2 then
    if u % 2 = 0 then 1 else (if v ≤ -1 then 0 else if v ≤ 0 then 1 else -2)
  else 0

/-- First coordinate of the square at index j of lap R: the closed-form path. -/
def squ (R j : ℤ) : ℤ :=
  if j < 0 then
    if R % 2 = 0 then (if j ≤ -R - 1 then 0 else if j ≤ -R then 1 else -j - R)
    else (if j ≤ -R - 2 then 3 else -j - R)
  else if j < 2 * R - 4 then -(R - 1) - j / 2 - j % 2
  else if j < 2 * R + 2 then (if j - (2 * R - 4) ≤ 2 then 3 - 2 * R else 2 - 2 * R)
  else if j < 6 * R - 5 then -(2 * R - 2) + (j - (2 * R + 2) + 1) / 2
  else if j < 6 * R + 1 then
    if j - (6 * R - 5) ≤ 0 then 0
    else if j - (6 * R - 5) ≤ 1 then 1
    else if j - (6 * R - 5) ≤ 2 then -1
    else j - (6 * R - 5) - 4
  else if j < 10 * R - 4 then 1 + (j - (6 * R + 1) + 2) / 2
  else if j < 10 * R + 2 then (if j - (10 * R - 4) ≤ 2 then 2 * R - 1 else 2 * R)
  else if j < 11 * R + 3 then 2 * R - (j - (10 * R + 2) + 1) / 2
  else if R % 2 = 0 then
    if (j - (11 * R + 3)) % 3 ≤ 0 then 3 * (R / 2) - 3 * ((j - (11 * R + 3)) / 3) - 2
    else 3 * (R / 2) - 3 * ((j - (11 * R + 3)) / 3) - 3
  else
    if (j - (11 * R + 3)) % 3 ≤ 1 then 3 * (R / 2) - 3 * ((j - (11 * R + 3)) / 3) - 1
    else 3 * (R / 2) - 3 * ((j - (11 * R + 3)) / 3) - 2

/-- Second coordinate of the square at index j of lap R. -/
def sqv (R j : ℤ) : ℤ :=
  if j < 0 then
    if R % 2 = 0 then R
    else (if j ≤ -R - 3 then R - 1 else R)
  else if j < 2 * R - 4 then R - 1 - j / 2
  else if j < 2 * R + 2 then
    if j - (2 * R - 4) ≤ 0 then 0
    else if j - (2 * R - 4) ≤ 1 then -1
    else if j - (2 * R - 4) ≤ 2 then 1
    else 4 - (j - (2 * R - 4))
  else if j < 6 * R - 5 then -1 - (j - (2 * R + 2) + 2) / 2
  else if j < 6 * R + 1 then (if j - (6 * R - 5) ≤ 2 then 2 - 2 * R else 1 - 2 * R)
  else if j < 10 * R - 4 then -(2 * R - 1) + (j - (6 * R + 1) + 1) / 2
  else if j < 10 * R + 2 then
    if j - (10 * R - 4) ≤ 0 then 0
    else if j - (10 * R - 4) ≤ 1 then 1
    else if j - (10 * R - 4) ≤ 2 then -1
    else j - (10 * R - 4) - 4
  else if j < 11 * R + 3 then 1 + (j - (10 * R + 2) + 2) / 2
  else if R % 2 = 0 then
    if (j - (11 * R + 3)) % 3 ≤ 1 then R / 2 + 2 + (j - (11 * R + 3)) / 3
    else R / 2 + 3 + (j - (11 * R + 3)) / 3
  else
    if (j - (11 * R + 3)) % 3 ≤ 0 then R / 2 + 2 + (j - (11 * R + 3)) / 3
    else R / 2 + 3 + (j - (11 * R + 3)) / 3

/-- Ring of (u, v): its spiral number is (2 ring - 1)² + rpos. -/
def ring (u v : ℤ) : ℤ := (if u ≥ 0 then u else -u) + (if v ≥ 0 then v else -v)

/-- Position of (u, v) on its ring, counted from the start of the ring. -/
def rpos (u v : ℤ) : ℤ :=
  if u > 0 then (if v ≥ 0 then 2 * u else 2 * u - 4 * v)
  else if u < 0 then (if v ≤ 0 then -6 * u - 4 * v else 8 * v - 6 * u)
  else (if v < 0 then -4 * v else 8 * v)

end Falafel
