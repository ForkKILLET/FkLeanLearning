import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Constructor

import MultiProof

open Function

namespace ReintroductionToProofs

-- Level 1: Product Symmetry

/-- For any types `A` and `B`, the product types `A × B` and `B × A` are equivalent. -/
proofs {A B : Type} : (A × B) ≃ (B × A) where

  | term :=
    ⟨ Prod.swap
    , Prod.swap
    , Eq.refl
    , Eq.refl
    ⟩

  | tactic := by
    fconstructor
    · exact Prod.swap
    · exact Prod.swap
    · intro; rfl
    · intro; rfl

-- Level 2: Coproduct Symmetry

/-- For any types `A` and `B`, the coproduct types `A ⊕ B` and `B ⊕ A` are equivalent. -/
proofs {A B : Type} : (A ⊕ B) ≃ (B ⊕ A) where

  | term :=
    ⟨ Sum.swap
    , Sum.swap
    , fun | .inl _ | .inr _ => rfl
    , fun | .inl _ | .inr _ => rfl
    ⟩

  | tactic := by
    fconstructor
    · exact Sum.swap
    · exact Sum.swap
    · intro x; cases x <;> rfl
    · intro x; cases x <;> rfl

-- Level 3: Swapping Inputs

/--
For any types `A`, `B`, and `C`,
the function types `A → B → C` and `B → A → C` are equivalent.
-/
example {A B C : Type} : (A → B → C) ≃ (B → A → C) :=
  ⟨ Function.swap
  , Function.swap
  , Eq.refl
  , Eq.refl
  ⟩

-- Level 4: Currying / Uncurrying

/--
For any types `A`, `B`, and `C`,
the function types `A × B → C` and `A → B → C` are equivalent.
-/
example {A B C : Type} : (A × B → C) ≃ (A → B → C) :=
  ⟨ Function.curry
  , Function.uncurry
  , Eq.refl
  , Eq.refl
  ⟩

-- Level 5: Component Functions

/--
For any types `X`, `A`, and `B`,
the types `X → A × B` and `(X → A) × (X → B)` are equivalent.
-/
example {X A B : Type} : (X → A × B) ≃ (X → A) × (X → B) :=
  ⟨ fun f => ⟨Prod.fst ∘ f, Prod.snd ∘ f⟩
  , fun ⟨fa, fb⟩ x => ⟨fa x, fb x⟩
  , Eq.refl
  , Eq.refl
  ⟩

-- Level 6: More Component Functions

/--
For any types `A`, `B`, and `C`,
the types `A ⊕ B → C` and `(A → C) × (B → C)` are equivalent.
-/
proofs {A B C : Type} : (A ⊕ B → C) ≃ (A → C) × (B → C) where

  | term :=
    ⟨ fun f => ⟨f ∘ Sum.inl, f ∘ Sum.inr⟩
    , fun ⟨fa, fb⟩ => Sum.elim fa fb -- `uncurry Sum.elim`
    , fun _ => funext fun | .inl _ | .inr _ => rfl
    , Eq.refl
    ⟩

  | tactic := by
    fconstructor
    · exact fun f => ⟨f ∘ Sum.inl, f ∘ Sum.inr⟩
    · exact fun ⟨fa, fb⟩ => Sum.elim fa fb
    · intro f
      ext s
      cases s <;> rfl
    · intro; rfl

-- Level 7: Boss Level

/-- The types `Unit ⊕ Unit` and `Bool` are equivalent. -/
proofs : Unit ⊕ Unit ≃ Bool where

  | term :=
    ⟨ fun | .inl _ => true | .inr _ => false
    , fun | true => .inl ⟨⟩ | false => .inr ⟨⟩
    , fun | .inl _ | .inr _ => rfl
    , fun | true | false => rfl
    ⟩

  | tactic := by
    fconstructor
    · exact fun | .inl _ => true | .inr _ => false
    · exact fun | true => .inl ⟨⟩ | false => .inr ⟨⟩
    · intro s; cases s <;> rfl
    · intro b; cases b <;> rfl

end ReintroductionToProofs
