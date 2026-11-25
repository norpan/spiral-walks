/-
The trapped pieces: the walk as a program.
25 Nov 2026. No Mathlib here: this file is compiled and run.

`check S ms L t` runs the walk of the piece with the moves `ms` for `L` moves and says whether
it then stands on the square with number `t` with every move leading to a visited square.
`S` is the store of the visited squares; there are two, one for the kernel and one for compiled code.
-/
import Std

set_option compiler.extract_closed false

namespace TrapCheck

/-- The number of a square on the square spiral; the same formula as `Falafel.spiral`. -/
def sp (p : Int × Int) : Int :=
  let x := p.1
  let y := p.2
  let r := max (max x (-x)) (max y (-y))
  if x = r ∧ y > -r then (2 * r - 1) * (2 * r - 1) + (y + r)
  else if y = r then (2 * r - 1) * (2 * r - 1) + 2 * r + (r - x)
  else if x = -r then (2 * r - 1) * (2 * r - 1) + 4 * r + (r - y)
  else (2 * r - 1) * (2 * r - 1) + 6 * r + (x + r)

/-- A store of visited squares. It only has to work for squares inside `box`. -/
structure VSet (V : Type) where
  empty : V
  mem : V → Int × Int → Bool
  ins : V → Int × Int → V
  box : Int × Int → Bool

/-- The square with the lowest number in a list. -/
def lowest : List (Int × Int) → Option (Int × Int)
  | [] => none
  | q :: l =>
    match lowest l with
    | none => some q
    | some b => if sp b < sp q then some b else some q

/-- The squares one move away from `p`. -/
def cands (ms : List (Int × Int)) (p : Int × Int) : List (Int × Int) :=
  ms.map fun d => (p.1 + d.1, p.2 + d.2)

/-- One step of the walk. `none` if there is no unvisited square to go to, or if a square one
move away is outside the box. -/
def step {V : Type} (S : VSet V) (ms : List (Int × Int)) (st : V × (Int × Int)) :
    Option (V × (Int × Int)) :=
  let cs := cands ms st.2
  if cs.all S.box then
    match lowest (cs.filter fun q => !S.mem st.1 q) with
    | none => none
    | some q => some (S.ins st.1 q, q)
  else none

def loop {V : Type} (S : VSet V) (ms : List (Int × Int)) :
    Nat → V × (Int × Int) → Option (V × (Int × Int))
  | 0, st => some st
  | n + 1, st =>
    match step S ms st with
    | none => none
    | some st' => loop S ms n st'

/-- The walk stands on square `t`, and every square one move away is visited. -/
def stuck {V : Type} (S : VSet V) (ms : List (Int × Int)) (t : Int) (st : V × (Int × Int)) : Bool :=
  sp st.2 == t && (cands ms st.2).all fun q => S.box q && S.mem st.1 q

def check {V : Type} (S : VSet V) (ms : List (Int × Int)) (L : Nat) (t : Int) : Bool :=
  S.box (0, 0) &&
  match loop S ms L (S.ins S.empty (0, 0), (0, 0)) with
  | none => false
  | some st => stuck S ms t st

/-- The state after `n` moves, for cutting a long run into pieces. -/
def stateAfter {V : Type} (S : VSet V) (ms : List (Int × Int)) (n : Nat) : Option (V × (Int × Int)) :=
  loop S ms n (S.ins S.empty (0, 0), (0, 0))

/-- Where the square (x, y) with -K ≤ x, y < W - K is kept. -/
def key (W K : Nat) (q : Int × Int) : Nat := (q.1 + K).toNat * W + (q.2 + K).toNat

def inBox (W K : Nat) (q : Int × Int) : Bool :=
  decide (0 ≤ q.1 + K) && decide (q.1 + K < W) && decide (0 ≤ q.2 + K) && decide (q.2 + K < W)

/-- The visited squares as the bits of one number. For the kernel. -/
def natSet (W K : Nat) : VSet Nat where
  empty := 0
  mem v q := v.testBit (key W K q)
  ins v q := v ||| (1 <<< key W K q)
  box := inBox W K

/-- The visited squares as an array. For compiled code. -/
def arrSet (W K : Nat) : VSet (Array Bool) where
  empty := Array.replicate (W * W) false
  mem v q := v.getD (key W K q) false
  ins v q := v.setIfInBounds (key W K q) true
  box := inBox W K

def knight : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]
def ferz : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def alfil : List (Int × Int) := [(2, 2), (2, -2), (-2, 2), (-2, -2)]
def dabbaba : List (Int × Int) := [(2, 0), (-2, 0), (0, 2), (0, -2)]
def priest : List (Int × Int) := ferz ++ knight
def kangaroo : List (Int × Int) := alfil ++ knight
def carpenter : List (Int × Int) := dabbaba ++ knight
def leopard : List (Int × Int) := ferz ++ alfil ++ knight

end TrapCheck
