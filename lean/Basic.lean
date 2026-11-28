/-!
# General notions, without Mathlib

The statement files use these few notions. Mathlib has them too; here each is one line of
plain Lean, so the project needs only Lean itself.
-/

/-- `ℕ` and `ℤ` are the natural numbers and the integers. -/
notation "ℕ" => Nat
notation "ℤ" => Int

/-- The absolute value of an integer, written `|x|`. -/
def Int.abs (x : ℤ) : ℤ := if 0 ≤ x then x else -x

macro:max atomic("|" noWs) a:term noWs "|" : term => `(Int.abs $a)

/-- `Even n`: `n = k + k` for some integer `k`. -/
def Even (n : ℤ) : Prop := ∃ k, n = k + k

/-- `Odd n`: `n = 2 * k + 1` for some integer `k`. -/
def Odd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

/-- `ExistsUnique p`, written `∃! x, p x`: exactly one `x` has `p x`. -/
def ExistsUnique {α : Sort _} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x

macro "∃!" x:ident ", " b:term : term => `(ExistsUnique fun $x => $b)

/-- A set of elements of `α`, given by the property of being in it. `a ∈ M` means `M a`. -/
def Set (α : Type _) : Type _ := α → Prop

instance {α : Type _} : Membership α (Set α) := ⟨fun M a => M a⟩

/-- Moves are subtracted coordinate by coordinate. -/
instance : Sub (ℤ × ℤ) := ⟨fun p q => (p.1 - q.1, p.2 - q.2)⟩

/-- `StrictMono f`: `f m < f n` whenever `m < n`. -/
def StrictMono (f : ℕ → ℤ) : Prop := ∀ ⦃m n : ℕ⦄, m < n → f m < f n

/-- `{a, b, c}` lists the elements of a set, and `M ∪ N` is the union. -/
instance {α : Type _} : Singleton α (Set α) := ⟨fun a b => b = a⟩
instance {α : Type _} : Insert α (Set α) := ⟨fun a M b => b = a ∨ M b⟩
instance {α : Type _} : Union (Set α) := ⟨fun M N a => M a ∨ N a⟩

/-- `Function.update f a b` is `f` with the value at `a` replaced by `b`. -/
def Function.update {α β : Type _} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x
