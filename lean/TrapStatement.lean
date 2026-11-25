import StraightStatement

/-!
# The trapped pieces: the statement

A piece is given by its set `M` of moves, as changes of (x, y). The square spiral is
`Falafel.spiral` of `Statement.lean`, and an infinite run of the walk is `Straight.IsWalk` of
`StraightStatement.lean`. This file says what a run of finitely many moves is, what it means to be
trapped, and that five pieces are trapped: after how many moves and on which square. It also says
that their walks begin with the terms that OEIS lists.

The proofs are in the folder `Trap`; `Trap/Theorems.lean` has the theorems.
-/
namespace Trap

open Falafel (spiral)
open Straight (IsWalk)

/-- `a 0, a 1, ..., a L` is a run of `L` moves of the walk of the piece with the moves `M`. It
starts on square 1 and visits no square twice. Each next square is one move away. Every square
one move away with a lower number than the next square was visited before. These are the
conditions of `Straight.IsWalk`, asked of the first `L` moves only. -/
structure IsRun (M : Set (ℤ × ℤ)) (L : ℕ) (a : ℕ → ℤ × ℤ) : Prop where
  start : a 0 = (0, 0)
  injective : ∀ m ≤ L, ∀ n ≤ L, a m = a n → m = n
  move : ∀ n < L, a (n + 1) - a n ∈ M
  lowest : ∀ n < L, ∀ q, q - a n ∈ M → spiral q < spiral (a (n + 1)) → ∃ m ≤ n, a m = q

/-- The piece is trapped after `L` moves on the square with the number `t`: there is a run of
`L` moves that ends on that square, and every square one move away from it was visited. The walk
then has `L + 1` terms, and `t` is the last one. -/
def TrappedAfter (M : Set (ℤ × ℤ)) (L : ℕ) (t : ℤ) : Prop :=
  ∃ a : ℕ → ℤ × ℤ, IsRun M L a ∧ spiral (a L) = t ∧ ∀ q, q - a L ∈ M → ∃ m ≤ L, a m = q

/-- The rule decides every move: two runs of the same piece agree as far as both go. -/
def RunsAgree : Prop :=
  ∀ M L (a b : ℕ → ℤ × ℤ), IsRun M L a → IsRun M L b → ∀ n ≤ L, a n = b n

/-- A trap is the end: a piece that is trapped after `L` moves has no run of more than `L` moves,
and no infinite run. -/
def TrapIsTheEnd : Prop :=
  ∀ M L t, TrappedAfter M L t →
    (∀ L' (b : ℕ → ℤ × ℤ), IsRun M L' b → L' ≤ L) ∧ ¬ ∃ a : ℕ → ℤ × ℤ, IsWalk M a

/-- Every run of the piece begins with the numbers of the list `l`, as far as the run goes. -/
def BeginsWith (M : Set (ℤ × ℤ)) (l : List ℤ) : Prop :=
  ∀ L (a : ℕ → ℤ × ℤ), IsRun M L a → ∀ n ≤ L, n < l.length → l[n]? = some (spiral (a n))

/-- The moves of the Knight, the Ferz, the Alfil and the Dabbaba. -/
def knight : Set (ℤ × ℤ) :=
  {(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)}
def ferz : Set (ℤ × ℤ) := {(1, 1), (1, -1), (-1, 1), (-1, -1)}
def alfil : Set (ℤ × ℤ) := {(2, 2), (2, -2), (-2, 2), (-2, -2)}
def dabbaba : Set (ℤ × ℤ) := {(2, 0), (-2, 0), (0, 2), (0, -2)}

/-- The Knight (OEIS A316667) has 2016 terms; the last is 2084. -/
def KnightTrapped : Prop := TrappedAfter knight 2015 2084

/-- The Priest, Ferz + Knight (A398717), has 1051 terms; the last is 858. -/
def PriestTrapped : Prop := TrappedAfter (ferz ∪ knight) 1050 858

/-- The Kangaroo, Alfil + Knight (A398779), has 59,677 terms; the last is 57,552. -/
def KangarooTrapped : Prop := TrappedAfter (alfil ∪ knight) 59676 57552

/-- The Carpenter, Dabbaba + Knight (A398965), has 253,925,076 terms; the last is 259,115,490. -/
def CarpenterTrapped : Prop := TrappedAfter (dabbaba ∪ knight) 253925075 259115490

/-- The Leopard, Ferz + Alfil + Knight (A399167), has 256,730,882 terms; the last is
267,545,105. -/
def LeopardTrapped : Prop := TrappedAfter (ferz ∪ alfil ∪ knight) 256730881 267545105

/-! The walks begin with the terms in the DATA lines of the OEIS entries, read 25 Nov 2026. -/

/-- The Knight's walk begins with the 66 terms of the DATA line of A316667. -/
def KnightBegins : Prop := BeginsWith knight
  [1, 10, 3, 6, 9, 4, 7, 2, 5, 8, 11, 14, 29, 32, 15, 12, 27, 24, 45, 20, 23, 44, 41, 18, 35,
    38, 19, 16, 33, 30, 53, 26, 47, 22, 43, 70, 21, 40, 17, 34, 13, 28, 25, 46, 75, 42, 69, 104,
    37, 62, 95, 58, 55, 86, 51, 48, 77, 114, 73, 108, 151, 68, 103, 64, 67, 36]

/-- The Priest's walk begins with the 81 terms of the DATA line of A398717. -/
def PriestBegins : Prop := BeginsWith (ferz ∪ knight)
  [1, 3, 6, 4, 2, 5, 8, 11, 9, 12, 14, 29, 10, 23, 7, 18, 15, 32, 30, 33, 13, 28, 25, 27, 24,
    45, 20, 22, 19, 16, 34, 17, 35, 38, 36, 39, 66, 63, 37, 62, 95, 58, 55, 31, 54, 85, 26, 47,
    76, 21, 40, 67, 64, 97, 60, 93, 56, 59, 92, 89, 57, 88, 53, 84, 49, 51, 48, 77, 44, 41, 68,
    103, 65, 98, 61, 94, 135, 90, 129, 86, 52]

/-- The Kangaroo's walk begins with the 71 terms of the DATA line of A398779. -/
def KangarooBegins : Prop := BeginsWith (alfil ∪ knight)
  [1, 10, 3, 6, 9, 4, 7, 2, 5, 8, 11, 14, 28, 13, 34, 12, 15, 18, 35, 38, 19, 16, 33, 29, 32,
    54, 27, 24, 45, 20, 23, 44, 41, 22, 40, 17, 61, 36, 39, 66, 63, 67, 64, 97, 37, 62, 95, 31,
    60, 30, 53, 25, 46, 21, 69, 42, 73, 108, 43, 70, 105, 148, 65, 98, 139, 59, 55, 58, 88, 57,
    94]

/-- The Carpenter's walk begins with the 77 terms of the DATA line of A398965. -/
def CarpenterBegins : Prop := BeginsWith (dabbaba ∪ knight)
  [1, 10, 3, 5, 2, 6, 9, 4, 7, 18, 15, 12, 27, 24, 11, 8, 19, 16, 14, 29, 31, 33, 30, 28, 13,
    34, 17, 40, 21, 23, 20, 39, 36, 61, 32, 55, 53, 26, 47, 22, 41, 43, 45, 42, 69, 38, 35, 37,
    62, 60, 58, 89, 54, 52, 25, 46, 44, 71, 73, 75, 72, 70, 68, 66, 63, 65, 67, 64, 97, 95, 93,
    56, 59, 57, 88, 86, 51]

/-- The Leopard's walk begins with the 76 terms of the DATA line of A399167. -/
def LeopardBegins : Prop := BeginsWith (ferz ∪ alfil ∪ knight)
  [1, 3, 6, 4, 2, 5, 8, 11, 9, 12, 14, 28, 10, 23, 7, 18, 15, 19, 16, 33, 13, 29, 32, 30, 53,
    25, 27, 24, 45, 20, 22, 40, 17, 34, 59, 31, 54, 85, 26, 47, 76, 21, 41, 44, 42, 69, 38, 35,
    39, 36, 61, 94, 56, 58, 55, 86, 51, 48, 52, 49, 78, 46, 75, 43, 70, 105, 37, 62, 95, 136,
    57, 88, 127, 84, 50, 79]

end Trap
