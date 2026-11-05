/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.AlgebraicLimitTheorem.PartIV

set_option autoImplicit false

open Finset

namespace RealAnalysisStory

-- Problem 1

/-- Theorem `Bdd_of_Conv`: Prove the statement. -/
theorem Bdd_of_Conv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) : SeqBdd a := by
  apply Bdd_of_ConvNonzero a L ha

-- Problem 2

/-- Prove the statement -/
example (N : ℕ) : ∃ k : ℕ, N * (N + 1) = 2 * k := by
  induction' N with N hN
  · use 0
  · choose k hk using hN
    use k + N + 1
    rewrite [(by ring_nf : 2 * (k + N + 1) = 2 * k + 2 * (N + 1))]
    rewrite [← hk]
    ring_nf

-- Problem 3

/-- Theorem `SumFirstN`: Prove the statement. -/
theorem SumFirstN (N : ℕ) : 2 * ∑ k ∈ range N, (k + 1) = N * (N + 1) := by
  induction' N with N hN
  · bound
  · rewrite [sum_range_succ]
    rewrite [(by ring_nf :
      2 * (∑ x ∈ range N, (x + 1) + (N + 1)) = 2 * ∑ x ∈ range N, (x + 1) + 2 * (N + 1)
    )]
    rewrite [hN]
    ring_nf

end RealAnalysisStory
