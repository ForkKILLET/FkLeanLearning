import Mathlib.Tactic.Use
import Mathlib.Tactic.Constructor

import MultiProof

open Classical

namespace ReintroductionToProofs

-- Level 1: Universal Truth

/-- For all `a : A`, `a = a` holds. -/
proofs {A : Type} : ∀ a : A, a = a where

  | term := fun _ => rfl -- `Eq.refl`

  | tactic := by intro; rfl

-- Level 2: More Transitivity

/-- For all `w x y z : A` if `w = x` and `x = y` and `y = z` then `w = z`. -/
proofs {A : Type} : ∀ w x y z : A, w = x → x = y → y = z → w = z where

  | tactic := by
    intro _ _ _ _ w_eq_x x_eq_y y_eq_z
    rw [w_eq_x, x_eq_y, y_eq_z]

  | term := fun _ _ _ _ w_eq_x x_eq_y y_eq_z =>
    (w_eq_x.trans x_eq_y).trans y_eq_z

-- Level 3: Universal Elimination

/--
Suppose the predicate `P : A → Prop` holds for all `x : A`.
Then for any particular element `a : A`, `P a` is true.
-/
example {A : Type} {P : A → Prop} (a : A) (h : ∀ x : A, P x) : P a := h a

-- Level 4: Introducing Existence

/-- There is some boolean `b` so that `b && b = b || b` -/
proofs : ∃ b : Bool, (b && b) = (b || b) where

  | term := ⟨true, rfl⟩

  | tactic_use := by
    use true
    rfl

  | tactic_constructor := by
    constructor
    case w => exact true
    case h => rfl

  | tactic_fconstructor := by
    fconstructor
    · exact true
    · rfl

-- Level 5: Injected Elements

/--
If `a : A` and `b : B` then the projections of `⟨a, b⟩ : A × B`
are definitionally equal to `a : A` and `b : B`, respectively.
-/
proofs {A B : Type}
    (x : A ⊕ B) : (∃ a : A, x = Sum.inl a) ∨ (∃ b : B, x = Sum.inr b) where

  | term := match x with
    | .inl a => .inl ⟨a, rfl⟩
    | .inr b => .inr ⟨b, rfl⟩

  | tactic := by
    cases x with
    | inl a => left; use a
    | inr b => right; use b

  | tactic_rcases := by
    rcases x with a | b
    · left; use a
    · right; use b

-- Level 6: Multiple Quantifiers

/--
For any type `A`, for all elements `x : A`,
there exists an element `y : A`, so that `x = y`.
-/
proofs {A : Type} : ∀ x : A, ∃ y : A, x = y where

  | term := fun x => ⟨x, rfl⟩

  | tactic := by
    intro x
    use x

-- Level 7: Commuting Quantifiers

/--
Given a family of propositions `P : A → B → Prop`,
`∃ z : B, ∀ w : A, P w z` implies `∀ x : A, ∃ y : B, P x y`
-/
example {A B : Type}
    (P : A → B → Prop) : (∃ z : B, ∀ w : A, P w z) → ∀ x : A, ∃ y : B, P x y :=
  fun ⟨z, all_w_pwz⟩ x => ⟨z, all_w_pwz x⟩

-- Level 8: Negating Existence

/--
Given a family of propositions `P : A → Prop`,
`∀ x : A, ¬ (P x)` is logically equivalent to `¬ (∃ x : A, P x)`
-/
theorem Exists.curry {T : Prop} {A : Type} {P : A → Prop}
  (f : (∃ x : A, P x) → T) : ∀ x : A, P x → T :=
  fun x px => f ⟨x, px⟩

theorem Exists.uncurry {T : Prop} {A : Type} {P : A → Prop}
  (f : ∀ x : A, P x → T) : (∃ x : A, P x) → T :=
  fun ⟨x, px⟩ => f x px

proofs {A : Type} {P : A → Prop} :
    (∀ x : A, ¬ P x) ↔ ¬ (∃ x : A, P x) where

  | term :=
    ⟨ fun all_x_npx ⟨x, px⟩ => all_x_npx x px
    , fun nsome_x_px x px => nsome_x_px ⟨x, px⟩
    ⟩

  | curry_uncurry := ⟨Exists.uncurry, Exists.curry⟩

  | tactic := by
    constructor
    · intro all_x_npx ⟨x, px⟩
      exact all_x_npx x px
    · intro nsome_x_px x px
      exact nsome_x_px ⟨x, px⟩

-- Level 9: Negating Universality

/--
Given a family of propositions `P : A → Prop`,
`∃ x : A, ¬ (P x)` implies `¬ (∀ x : A, P x)`
-/
proofs {A : Type} {P : A → Prop} :
    (∃ x : A, ¬ P x) → ¬ (∀ x : A, P x) where

  | term := fun ⟨x, npx⟩ all_x_px => npx $ all_x_px x

-- Level 10: Boss Level

/--
Given a family of propositions `P : A → Prop`,
using classical logic, `¬ (∀ x : A, P x)` implies `∃ x : A, ¬ (P x)`.
-/
proofs {A : Type} (P : A → Prop) :
    ¬ (∀ x : A, P x) → ∃ x : A, ¬ P x where

  | term := fun nall_x_px => byContradiction fun nsome_x_npx =>
    nall_x_px fun x => byContradiction fun npx =>
      nsome_x_npx ⟨x, npx⟩

  | tactic := by
    intro nall_x_px
    apply byContradiction
    intro nsome_x_npx
    apply nall_x_px
    intro x
    apply byContradiction
    intro npx
    apply nsome_x_npx
    exact ⟨x, npx⟩

end ReintroductionToProofs
