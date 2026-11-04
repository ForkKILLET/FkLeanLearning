/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

open Finset

namespace RealAnalysisStory

-- Level 1: Finite Sums

/-- Theorem `TermLeSum`: Prove this -/
theorem TermLeSum
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X]
    (a : ℕ → X) (N : ℕ) : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
  induction' N with D hD
  · intro n hn
    contradiction
  · intro n hn
    rewrite [sum_range_succ]
    by_cases hn' : n < D
    · specialize hD n hn'
      have haD : |a D| ≥ 0 := by bound
      bound
    · rewrite [(by bound : n = D)]
      have hsumd : ∑ i ∈ range D, |a i| ≥ 0 := by
        apply sum_nonneg
        intro i hi
        bound
      bound

-- Level 2: Bounded

/-- Theorem `Bdd_of_ConvNonzero`: Prove this -/
theorem Bdd_of_ConvNonzero (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (_hL : L ≠ 0) : SeqBdd a := by
  specialize ha 1 (by bound)
  choose N hN using ha
  let sum := ∑ k ∈ range N, |a k|
  have hsum : sum ≥ 0 := by
    apply sum_nonneg
    intro i hi
    bound
  use sum + |L| + 1
  have hLabs : |L| ≥ 0 := by bound

  split_ands
  · bound
  · intro n
    by_cases hn : n < N
    · have han : |a n| ≤ sum := TermLeSum a N n hn
      bound
    · specialize hN n (by bound)
      have htri := abs_add_le (a n - L) L
      ring_nf at htri
      linarith only [htri, hN, hsum]

end RealAnalysisStory
