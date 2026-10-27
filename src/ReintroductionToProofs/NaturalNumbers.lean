import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Use

import MultiProof

open Nat (succ)
open Classical

set_option autoImplicit false

namespace ReintroductionToProofs

-- Level 1: Numerals

/--
Explicit numerals `1`, `2`, `3`, `4`, and so on
are defined as repeated successors of the previous numerals.
-/
example :
    (1 = succ 0) ∧ (2 = succ 1) ∧ (3 = succ 2) ∧ (4 = succ 3) ∧
    (9223372036854775809 = succ 9223372036854775808) := by
  repeat constructor

-- Level 2: Normal Forms

/--
Arithmetic equations involving explicit numerals such as `12 + 23 = 5 * (4 + 3)`
hold by `rfl`.
-/
example :
    (2 + 2 = 4) ∧ (1 + 5 = 2 * 3) ∧ (12 + 23 = 5 * (4 + 3)) ∧
    (2 * 5 = 5 * 2) ∧ ((3 + 1) + 2 = 2 + (1 + 3)) := by
  repeat constructor

-- Level 3: Induction

/-- Every natural number is even or odd. -/
proofs : ∀ n : ℕ , (∃ m : ℕ, n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1) where

  | tactic := by
    intro n
    induction n with
    | zero =>
      left
      use 0
    | succ _ ih =>
      match ih with
      | .inl ⟨m, hm⟩ =>
        right
        use m
        exact congrArg succ hm
      | .inr ⟨m, hm⟩ =>
        left
        use m + 1
        exact congrArg succ hm

  | term := Nat.rec
    (.inl ⟨0, rfl⟩)
    fun _ => fun
      | .inl ⟨m, hm⟩ => .inr ⟨m, congrArg succ hm⟩
      | .inr ⟨m, hm⟩ => .inl ⟨m + 1, congrArg succ hm⟩

-- Level 4: Recursion

/-- There is a function `pred : ℕ → ℕ` that sends `0` to `0` and `succ n` to `n`. -/
proofs : ∃ f : ℕ → ℕ, (f 0 = 0) ∧ (∀ n : ℕ, f (succ n) = n) where

  | term :=
    ⟨ fun | 0 => 0 | succ n => n
    , rfl
    , fun _ => rfl
    ⟩

  | tactic := by
    use fun | 0 => 0 | succ n => n
    constructor
    · rfl
    · intro; rfl

-- Level 5: Predecessor of Successor

/-- The composite of `succ : ℕ → ℕ` followed by `pred : ℕ → ℕ` is the identity function. -/
theorem Nat.pred_comp_succ : _root_.Nat.pred ∘ succ = id := rfl

-- Level 6: Defining Addition

/-- For all natural numbers `m` and `n`, `n + 0 = n` and `m + (succ n) = succ (m + n)`. -/
example : (∀ n : ℕ, (n + 0 = n)) ∧ (∀ m n : ℕ, m + (succ n) = succ (m + n)) :=
  ⟨ fun _ => rfl
  , fun _ _ => rfl
  ⟩

-- Level 7: Adding Zero

/-- For all natural numbers `n`, `n + 0 = n` and `0 + n = n`. -/
proofs : ∀ n : ℕ, (n + 0 = n) ∧ (0 + n = n) where

  | tactic := by
    intro n
    constructor
    · rfl
    · induction n with
      | zero =>
        rfl
      | succ n' ih =>
        exact congrArg succ ih

  | term := Nat.rec
    ⟨rfl, rfl⟩
    fun _ ⟨_, ih⟩ => ⟨rfl, congrArg succ ih⟩

  | term_break_conj_first := fun n =>
    ⟨ rfl
    , Nat.rec rfl (fun _ => congrArg succ) n
    ⟩

-- Level 8: Adding Successors

/--
For all natural numbers `m n`,
`m + succ n = succ (m + n)` and `succ m + n = succ (m + n)`.
-/
proofs : ∀ m n : ℕ, m + succ n = succ (m + n) ∧ succ m + n = succ (m + n) where

  | tactic := by
    intro m n
    constructor
    · rfl
    · induction n with
      | zero =>
        rfl
      | succ n' ih =>
        exact congrArg succ ih

  | term := fun _ => Nat.rec
    ⟨rfl, rfl⟩
    fun _ ⟨_, ih⟩ => ⟨rfl, congrArg succ ih⟩

  | term_break_conj_first := fun _ n =>
    ⟨ rfl
    , Nat.rec rfl (fun _ => congrArg succ) n
    ⟩

-- Level 9: Commuting Addition

/-- For all natural numbers `m n`, `m + n = n + m`. -/
proofs : ∀ m n : ℕ, m + n = n + m where

  | tactic := by
    intro m n
    induction n with
    | zero =>
      rw [Nat.zero_add]
      rfl
    | succ n' ih =>
      rw [Nat.succ_add]
      exact congrArg succ ih

  | term := fun m => Nat.rec
    (Nat.zero_add m).symm
    fun n' ih => (Nat.succ_add n' m).symm ▸ congrArg succ ih

-- Level 10: Successor Injectivity

/-- The successor function is injective. -/
theorem Nat.succ_injective : ∀ m n : ℕ, succ m = succ n → m = n := fun _ _ =>
  congrArg _root_.Nat.pred

-- Level 11: Boss Level

/-- Zero is not the successor of any natural number. -/
proofs : ¬ (∃ n : ℕ, succ n = 0) where

  | no_match := fun ⟨_, sn_eq_zero⟩ => nomatch sn_eq_zero

  | no_confusion := fun ⟨_, sn_eq_zero⟩ => Nat.noConfusion sn_eq_zero

  | term := fun ⟨_, sn_eq_zero⟩ =>
    let discriminator : ℕ → Prop := fun
      | 0 => False
      | succ _ => True
    have true_eq_false : True = False := congrArg discriminator sn_eq_zero
    true_eq_false ▸ ⟨⟩

end ReintroductionToProofs
