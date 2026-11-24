import Mathlib

/-!
# Two tactics for case analysis on `if`

The model is made of nested `if ... then ... else`. `split_ifs` would produce every combination
of cases, most of them impossible. These two tactics split one `if` at a time and drop a case as
soon as `omega` finds its conditions contradictory.
-/

/-- Split every `if` in the goal and discard the cases with contradictory conditions. -/
macro "split_cases" : tactic =>
  `(tactic| repeat' (first | (exfalso; omega) | split))

/-- `split_cases`, then close every remaining case with `omega`. -/
macro "split_omega" : tactic =>
  `(tactic| repeat' (first | (exfalso; omega) | split | omega))
