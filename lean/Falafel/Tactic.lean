import Statement

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

/-- Mathlib's `split_ifs`, for `if` in the goal only: split one `if` at a time. -/
macro "split_ifs" : tactic => `(tactic| repeat' split)

/-- Unfold `|x|` into `if` so that `omega` can use it. -/
macro "abs_omega" : tactic => `(tactic| ((try simp only [Int.abs] at *) <;> omega))

theorem Int.even_iff {n : ℤ} : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨_, h⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩

theorem Int.odd_iff {n : ℤ} : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨_, h⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩

attribute [refl] Int.le_refl Nat.le_refl

/-- Multiplying by a positive integer keeps `≤`. -/
theorem Int.scale_le {s a b : ℤ} (hs : 0 < s) (h : a ≤ b) : s * a ≤ s * b := by
  have := Int.mul_nonneg (Int.le_of_lt hs) (show 0 ≤ b - a by omega); grind

/-- Multiplying by a positive integer keeps `<`. -/
theorem Int.scale_lt {s a b : ℤ} (hs : 0 < s) (h : a < b) : s * a < s * b := by
  have := Int.mul_nonneg (Int.le_of_lt hs) (show 0 ≤ b - a - 1 by omega); grind

@[simp] theorem Set.mem_singleton_iff {α : Type _} {a b : α} : b ∈ ({a} : Set α) ↔ b = a := Iff.rfl
@[simp] theorem Set.mem_insert_iff {α : Type _} {a b : α} {M : Set α} :
    b ∈ (insert a M : Set α) ↔ b = a ∨ b ∈ M := Iff.rfl
@[simp] theorem Set.mem_union {α : Type _} {a : α} {M N : Set α} :
    a ∈ M ∪ N ↔ a ∈ M ∨ a ∈ N := Iff.rfl

instance (n : ℤ) : Decidable (Even n) := decidable_of_iff _ Int.even_iff.symm
instance (n : ℤ) : Decidable (Odd n) := decidable_of_iff _ Int.odd_iff.symm

/-- `{x | p x}`: the set of `x` with `p x`. -/
def Set.ofPred {α : Type _} (p : α → Prop) : Set α := p

macro "{" x:ident " | " p:term "}" : term => `(Set.ofPred fun $x => $p)

@[ext] theorem Set.ext {α : Type _} {M N : Set α} (h : ∀ a, a ∈ M ↔ a ∈ N) : M = N :=
  funext fun a => propext (h a)

@[simp] theorem Set.mem_ofPred_eq {α : Type _} {p : α → Prop} {a : α} :
    (a ∈ Set.ofPred p) = p a := rfl

@[simp] theorem Prod.fst_sub (p q : ℤ × ℤ) : (p - q).1 = p.1 - q.1 := rfl
@[simp] theorem Prod.snd_sub (p q : ℤ × ℤ) : (p - q).2 = p.2 - q.2 := rfl

theorem Function.update_apply {α β : Type _} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    Function.update f a b x = if x = a then b else f x := rfl
@[simp] theorem Function.update_self {α β : Type _} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b a = b := by simp [Function.update]
theorem Function.update_of_ne {α β : Type _} [DecidableEq α] {x a : α} (h : x ≠ a) (b : β)
    (f : α → β) : Function.update f a b x = f x := by simp [Function.update, h]

/-- Mathlib's `split_ifs at h with hi`, for one `if` in `h`: the case whose `h` is false
(`none = some _`) is closed by `simp`. -/
macro "split_ifs" " at " h:ident " with " hi:ident : tactic =>
  `(tactic| ((split at $h:ident <;> rename_i $hi:ident) <;> (try (simp at $h:ident; done))))

theorem List.find?_congr {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (List.mem_cons_self ..),
      List.find?_congr fun x hx => h x (List.mem_cons_of_mem a hx)]
