/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

-- Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Logic.Function.Iterate

-- Tactic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Push

-- Project
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Tactic compatibility

open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| push $cfg:optConfig Not $[$loc]?)

open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig : conv =>
  `(conv| push $cfg:optConfig Not)

-- Definitions

/--
For a sequence `a : ℕ → X` and an element `L : X`,
we say that `SeqLim a L` holds if: for every `ε > 0`,
there exists `N : ℕ` such that for all `n ≥ N`, we have `|a n - L| < ε`.
-/
def SeqLim {X : Type*} [Lattice X] [AddGroup X] (a : ℕ → X) (L : X) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

/--
A sequence `a : ℕ → X` converges (`SeqConv a` holds) if
there exists some `L : X` so that `a → L`, that is, `SeqLim a L` holds.
-/
def SeqConv {X : Type*} [Lattice X] [AddGroup X] (a : ℕ → X) : Prop :=
  ∃ L, SeqLim a L

/--
A sequence `a : ℕ → X` is bounded (`SeqBdd` holds) if
there exists some positive `M : X` so that `|a n| ≤ M`, for all `n`.
-/
def SeqBdd {X : Type*} [Lattice X] [AddGroup X] (a : ℕ → X) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

/--
A sequence `a : ℕ → X` is bounded by (`SeqBddBy` holds) `M : X` if, for all `n`, `a n ≤ M`.
-/
def SeqBddBy {X : Type*} [Preorder X] (a : ℕ → X) (M : X) : Prop :=
  ∀ n, a n ≤ M

/--
A sequence `σ : ℕ → ℕ` is a _subsequence_ if `∀ i j, i < j → σ i < σ j`.
-/
def Subseq (σ : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → σ i < σ j

/--
For a sequence `a : ℕ → X` is said to satisfy `IsCauchy` (that is, the sequence "is Cauchy") if:
for every `ε > 0`, there exists `N : ℕ` such that for all `n ≥ N` and `m ≥ n`,
we have `|a m - a n| < ε`.
-/
def IsCauchy {X : Type*} [Lattice X] [AddGroup X] (a : ℕ → X) : Prop :=
  ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε

-- Theorems

/-- The triangle inequality. -/
theorem abs_add {X : Type*} [Lattice X] [AddCommGroup X] [AddLeftMono X] (x y : X) :
    |x + y| ≤ |x| + |y| :=
  _root_.abs_add_le x y

/-- If `x ≠ 0`, then `0 < |x|`. -/
theorem abs_pos_of_nonzero {x : ℝ} (h : x ≠ 0) : 0 < |x| :=
  abs_pos.2 h

/-- The absolute value function is Lipschitz with constant `1`. -/
theorem abs_Lipschitz {x y : ℝ} : |(|x| - |y|)| ≤ |x - y| :=
  abs_abs_sub_abs_le x y

/-- If `0 < |x|`, then `x ≠ 0`. -/
theorem nonzero_of_abs_pos {x : ℝ} (h : 0 < |x|) : x ≠ 0 :=
  abs_pos.1 h

/-- For a function `σ : ℕ → ℕ`, we have that: `σ (σ^[k]) = σ^[k+1]`. -/
theorem succ_iterate (σ : ℕ → ℕ) (k n : ℕ) : σ (σ^[k] n) = σ^[k + 1] n :=
  (Function.iterate_succ_apply' σ k n).symm

/-- If a natural number `n ≠ 0`, then `1 ≤ n`. -/
theorem ge_one_of_nonzero {n : ℕ} (h : n ≠ 0) : 1 ≤ n := by omega

/--
For a function `σ : ℕ → ℕ`, if `σ n < σ (n + 1)`, then for any `i < j`, `σ i < σ j` --
that is, `Subseq σ` holds.
-/
theorem subseq_of_succ (σ : ℕ → ℕ) (hσ : ∀ n, σ n < σ (n + 1)) : Subseq σ := by
  apply strictMono_nat_of_lt_succ hσ

/--
If `a` is `Antitone`, then `-a` is `Monotone`.
-/
theorem MonotoneNeg_of_Antitone
    {X : Type*} [LinearOrder X] [AddCommGroup X] [IsOrderedAddMonoid X]
    (a : ℕ → X) (ha : Antitone a) : Monotone (-a) := by
  intro m n hmn
  apply ha at hmn
  rewrite [show (-a) m = - a m by rfl]
  rewrite [show (-a) n = - a n by rfl]
  bound

/-- If `a` satisfies `IsCauchy`, then `-a` does too. -/
theorem IsCauchyNeg
    {X : Type*} [NormedField X] [Lattice X] (a : ℕ → X) (ha : IsCauchy a) : IsCauchy (-a) := by
  intro ε ε_pos
  specialize ha ε ε_pos
  let ⟨N, ha⟩ := ha
  use N
  intro n hn m hm
  specialize ha n hn m hm
  rewrite [show (-a) m = -a m by rfl]
  rewrite [show (-a) n = -a n by rfl]
  rewrite [show -a m - -a n = -(a m - a n) by ring_nf]
  rewrite [abs_neg]
  apply ha

end RealAnalysisStory
