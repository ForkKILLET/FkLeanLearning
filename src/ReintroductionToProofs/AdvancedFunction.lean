import Mathlib.Tactic.Use

import MultiProof

open Classical

namespace ReintroductionToProofs

-- Level 1: Total Functions

/--
A function `f : A → B` must be *total*
meaning for each `a : A` there is some `b : B` so that `f a = b`.
-/
theorem Function.total {A B : Type} (f : A → B) :
    ∀ a : A, ∃ b : B, f a = b :=
  fun a => ⟨f a, rfl⟩

-- Level 2: Surjectivity

/-- The function `not : Bool → Bool` is surjective. -/
theorem Bool.not_surjective : ∀ b : Bool, ∃ x : Bool, not x = b := fun
  | true => ⟨false, rfl⟩
  | false => ⟨true, rfl⟩

-- Level 3: Canceling Surjectivity

/-- For functions `f : A → B` and `g : B → C` if `g ∘ f` is surjective, then so is `g`. -/
theorem Function.Surjective.of_comp {A B C : Type}
    (f : A → B) (g : B → C)
    (gf_is_surj : ∀ z : C, ∃ x : A, (g ∘ f) x = z) :
    ∀ c : C, ∃ y : B, g y = c :=
  fun c =>
    let ⟨x, gfx_eq_c⟩ := gf_is_surj c
    ⟨f x, gfx_eq_c⟩

-- Level 4: Composing Surjectivity

/--
If `f : A → B` and `g : B → C` are both surjective then `g ∘ f : A → C` is also surjective. -/
proofs Function.Surjective.comp {A B C : Type}
    (f : A → B) (g : B → C)
    (f_is_surj : ∀ b : B, ∃ a : A, f a = b)
    (g_is_surj : ∀ c : C, ∃ b : B, g b = c) :
    ∀ c : C, ∃ a : A, (g ∘ f) a = c where

  | term := fun c =>
    let ⟨b, gb_eq_c⟩ := g_is_surj c
    let ⟨a, fa_eq_b⟩ := f_is_surj b
    have gfa_eq_c : g (f a) = c := fa_eq_b ▸ gb_eq_c
    ⟨a, gfa_eq_c⟩

  | tactic := by
    intro c
    let ⟨b, hb⟩ := g_is_surj c
    let ⟨a, ha⟩ := f_is_surj b
    rw [← ha] at hb
    exact ⟨a, hb⟩

-- Level 5: Injectivity

/-- The function `not : Bool → Bool` is injective. -/
theorem Bool.not_injective : ∀ x y : Bool, not x = not y → x = y :=
  fun x y h =>
    match x, y with
    | true, true | false, false => rfl
    | true, false | false, true => nomatch h

-- Level 6: Composing Injectivity

/--
If `f : A → B` and `g : B → C` are both injective functions,
then `g ∘ f : A → C` is also injective.
-/
proofs Function.Injective.comp {A B C : Type}
    (f : A → B) (g : B → C)
    (f_is_inj : ∀ x y : A, f x = f y → x = y)
    (g_is_inj : ∀ x y : B, g x = g y → x = y) :
    ∀ x y : A, (g ∘ f) x = (g ∘ f) y → x = y where

  | term := fun x y gfx_eq_gfy =>
    have fx_eq_fy := g_is_inj (f x) (f y) gfx_eq_gfy
    have x_eq_y := f_is_inj x y fx_eq_fy
    x_eq_y

  | term_short := fun x y gfx_eq_gfy =>
    f_is_inj x y $ g_is_inj (f x) (f y) gfx_eq_gfy

  | tactic := by
    intro x y gfx_eq_gfy
    apply f_is_inj x y
    apply g_is_inj (f x) (f y)
    exact gfx_eq_gfy

-- Level 7: Canceling Injectivity

/-- For functions `f : A → B` and `g : B → C` if `g ∘ f` is injective, then so is `f`. -/
proofs Function.Injective.of_comp {A B C : Type}
    (f : A → B) (g : B → C)
    (gf_is_inj : ∀ x y : A, (g ∘ f) x = (g ∘ f) y → x = y) :
    ∀ x y : A, f x = f y → x = y where

  | term := fun x y fx_eq_fy =>
    have gfx_eq_gfy := congrArg g fx_eq_fy
    have x_eq_y := gf_is_inj x y gfx_eq_gfy
    x_eq_y

  | term_short := fun x y => gf_is_inj x y ∘ congrArg g

  | tactic := by
    intro x y fx_eq_fy
    apply gf_is_inj x y
    exact congrArg g fx_eq_fy

-- Level 8: Bijectivity

/-- The function `not : Bool → Bool` is bijective. -/
theorem Bool.not_bijective :
    (∀ x y : Bool, not x = not y → x = y) ∧ (∀ x : Bool, ∃ y : Bool, not y = x) :=
  ⟨Bool.not_injective, Bool.not_surjective⟩

-- Level 9: Invertibility

/-- The function `not : Bool → Bool` is invertible. -/
proofs Bool.not_invertible :
    ∃ g : Bool → Bool,
    (∀ b : Bool, g (not b) = b) ∧ (∀ b : Bool, not (g b) = b) where

  | term :=
    let cases_bool := fun | true | false => rfl
    ⟨not, ⟨cases_bool, cases_bool⟩⟩

  | tactic := by
    apply Exists.intro not
    constructor <;> intro b <;> cases b <;> rfl

-- Level 10: Inverse Invertibility

/-- The inverse of an invertible function is invertible. -/
example {A B : Type}
    (f : A → B) (g : B → A)
    (inv : (∀ a : A, g (f a) = a) ∧ (∀ b : B, f (g b) = b)) :
    ∃ h : A → B, (∀ b : B, h (g b) = b) ∧ (∀ a : A, g (h a) = a) :=
  ⟨f, And.symm inv⟩

-- Level 11: Invertible Implies Bijective

/-- An invertible function is bijective. -/
proofs Function.bijective_of_invertible {A B : Type}
    (f : A → B)
    (inv : ∃ g : B → A, (∀ a : A, g (f a) = a) ∧ (∀ b : B, f (g b) = b)) :
    (∀ x y : A, f x = f y → x = y) ∧ (∀ b : B, ∃ x : A, f x = b) where

  | term :=
    let ⟨g, left_inv, right_inv⟩ := inv
    ⟨ fun x y fx_eq_fy => left_inv x ▸ left_inv y ▸ congrArg g fx_eq_fy
    , fun b => ⟨g b, right_inv b⟩
    ⟩

  | tactic := by
    let ⟨g, left_inv, right_inv⟩ := inv
    constructor
    · intro x y fx_eq_fy
      rw [← left_inv x, ← left_inv y]
      exact congrArg g fx_eq_fy
    · intro b
      apply Exists.intro (g b)
      exact right_inv b

-- Level 12: Bijective Implies Invertible

/-- A bijective function is invertible. -/
proofs Function.invertible_of_bijective {A B : Type}
  (f : A → B)
  (inj : ∀ x y : A, f x = f y → x = y) (surj : ∀ b : B, ∃ x : A, f x = b) :
  ∃ g : B → A, (∀ a : A, g (f a) = a) ∧ (∀ b : B, f (g b) = b) where

  | term :=
    let g := fun b => (surj b).choose
    have gfa_eq_a : ∀ a : A, g (f a) = a := fun a =>
      inj (g $ f a) a (surj $ f a).choose_spec
    have fgb_eq_b : ∀ b : B, f (g b) = b := fun b =>
      (surj b).choose_spec
    ⟨g, gfa_eq_a, fgb_eq_b⟩

  | tactic := by
    let g := fun b => (surj b).choose
    use g
    constructor
    · intro a
      apply inj (g $ f a) a
      exact (surj $ f a).choose_spec
    · intro b
      exact (surj b).choose_spec

-- Level 13: Function Extensionality

/-- For functions `f g : A → B` if `∀ x : A, f x = g x` then `f = g`. -/
proofs {A B : Type} {f g : A → B} (p : ∀ x : A, f x = g x) : f = g where

  | tactic := by
    ext x
    exact p x

  | term := funext p

  | tactic_apply := by
    apply funext
    exact p

-- Level 14: Double Negation

/-- The composite of the function `not : Bool → Bool` with itself equals the identity function -/
proofs Bool.not_involutive : not ∘ not = id where

  | tactic := by
    ext x
    cases x <;> rfl

  | term := funext fun | true | false => rfl

-- Level 15: Isomorphism

/-- The function `f : A → B` is an isomorphism if and only if `f` is invertible. -/
proofs Function.isomorphism_iff_invertible {A B : Type}
  (f : A → B) :
  (∃ g : B → A, g ∘ f = id ∧ f ∘ g = id) ↔
  (∃ g : B → A, (∀ a : A, g (f a) = a) ∧ (∀ b : B, f (g b) = b)) where

  | term :=
    ⟨ fun ⟨g, gf_is_id, fg_is_id⟩ =>
        ⟨g, congrFun gf_is_id, congrFun fg_is_id⟩
    , fun ⟨g, gfa_eq_a, fgb_eq_b⟩ =>
        ⟨g, funext gfa_eq_a, funext fgb_eq_b⟩
    ⟩

  | tactic := by
    constructor
    · intro ⟨g, gf_is_id, fg_is_id⟩
      use g
      constructor
      · exact congrFun gf_is_id
      · exact congrFun fg_is_id
    · intro ⟨g, gfa_eq_a, fgb_eq_b⟩
      use g
      constructor
      · ext x
        exact gfa_eq_a x
      · ext x
        exact fgb_eq_b x

-- Level 16: Boss Level

/--
If `f : A → A → B` is surjective as a function from `A` to `A → B`,
then any endomorphism of `B` has a fixed point.
-/
proofs Function.Lawvere_fixed_point {A B : Type}
  (f : A → A → B) :
  (∀ g : A → B, ∃ a : A, f a = g) → (∀ n : B → B, ∃ b : B, n b = b) where

  | term := fun f_surj n =>
    let g : A → B := fun a => n (f a a)
    let ⟨ag, fag_eq_g⟩ := f_surj g
    ⟨f ag ag, (congrFun fag_eq_g ag).symm⟩

  | tactic := by
    intro f_surj n
    let g : A → B := fun a => n (f a a)
    let ⟨ag, fag_eq_g⟩ := f_surj g
    use f ag ag
    symm
    exact congrFun fag_eq_g ag

end ReintroductionToProofs
