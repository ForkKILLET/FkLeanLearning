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
For a sequence `a : ℕ → ℝ` and a real number `L : ℝ`,
we say that `SeqLim a L` holds if: for every `ε > 0`,
there exists `N : ℕ` such that for all `n ≥ N`, we have `|a n - L| < ε`.
-/
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

/--
A sequence `a : ℕ → ℝ` converges (`SeqConv a` holds) if
there exists some `L : ℝ` so that `a → L`, that is, `SeqLim a L` holds.
-/
def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

/--
A sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is bounded (`SeqBdd` holds) if
there exists some positive `M : X` so that `|a n| ≤ M`, for all `n`.
-/
def SeqBdd {X : Type} [Lattice X] [AddGroup X] (a : ℕ → X) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

-- Theorems

/-- If a natural number `n ≠ 0`, then `1 ≤ n`. -/
theorem ge_one_of_nonzero {n : ℕ} (h : n ≠ 0) : 1 ≤ n := by omega

end RealAnalysisStory
