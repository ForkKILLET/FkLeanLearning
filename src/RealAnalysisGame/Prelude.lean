/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

-- Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

-- Tactic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases

-- Project
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

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

-- Theorems

/-- If a natural number `n ≠ 0`, then `1 ≤ n`. -/
theorem ge_one_of_nonzero {n : ℕ} (h : n ≠ 0) : 1 ≤ n := by omega

end RealAnalysisStory
