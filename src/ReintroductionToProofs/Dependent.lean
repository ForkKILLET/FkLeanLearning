import Mathlib.Logic.Equiv.Defs

import MultiProof

namespace ReintroductionToProofs

-- Level 1: Types

/-- Define any dependent family of types indexed by the type of booleans. -/
proofs : (Bool → Type) where
  | const := fun _ => Bool
  | non_const := fun | true => Unit | false => Unit × Unit
  | no_inst := fun | true => Unit | false => Empty

-- Level 2: Functions

/-- The polymorphic identity function has type `(A : Type) → A → A`. -/
proofs : (A : Type) → A → A where
  | id := fun _ => id
  | explicit_id := fun (A : Type) (a : A) => id (α := A) a
  | at_id := fun (A : Type) (a : A) => @id A a
  | at_id_eta := @id

-- Level 3: Application

/--
Given a pair of type families `B C : A → Type`
and a fiberwise function `f : (x : A) → B x → C x`,
then there is a function from sections of the first type family
to sections of the second type family.
-/
example {A : Type} {B C : A → Type} (f : (x : A) → B x → C x) :
    ((y : A) → B y) → ((z : A) → C z) :=
  fun aBa a => f a (aBa a)

-- Level 4: Pairs

/--
The dependent pair type `(x : A) × B x` has a pair of projection functions,
sending a dependent pair to its first and second components respectively.
-/
proofs {A : Type} {B : A → Type} :
    ((x : A) × B x → A) × ((p : (x : A) × B x) → B p.1) where

  | lambda :=
    ⟨ fun ⟨a, _⟩ => a
    , fun ⟨_, ba⟩ => ba
    ⟩

  | sigma := ⟨Sigma.fst, Sigma.snd⟩

-- Level 5: Currying

/--
There is an equivalence between
the type of dependent functions out of the dependent pair type `(x : A) × B x`
and the type of dependent functions of two variables `x : A` and `y : B x`
defined by currying and uncurrying.
-/
example {A : Type} {B : A → Type} {C : (x : A) × B x → Type} :
    ((p : (x : A) × B x) → C p) ≃ ((x : A) → (y : B x) → C ⟨x, y⟩) :=
  ⟨ fun f a ba => f ⟨a, ba⟩ -- `Sigma.curry`
  , fun g ⟨a, ba⟩ => g a ba -- `Sigma.uncurry`
  , fun _ => rfl
  , fun _ => rfl
  ⟩

-- Level 6: Boss Level

/--
The type theoretic axiom of choice characterizes dependent functions
into a dependent pair type.
-/
example {A : Type} {B : A → Type} (C : (x : A) → B x → Type) :
    ((x : A) → (y : B x) × C x y) ≃ ((s : (x : A) → B x) × ((x : A) → C x (s x))) :=
  ⟨ fun h => ⟨fun x => (h x).fst, fun x => (h x).snd⟩
  , fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩
  , fun _ => rfl
  , fun _ => rfl
  ⟩

end ReintroductionToProofs
