/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Theorem `Pset8Ex1`: Prove the statement. -/
theorem Pset8Ex1 (n : ℕ) : 2 * n + 9 ≤ 2 ^ (n + 4) := by
  induction' n with n hn
  · bound
  · ring_nf at hn ⊢
    bound

-- Problem 2

/-- Prove the statement. -/
example : ∃ N, ∀ n, (n + N) ^ 2 ≤ 2 ^ (n + N) := by
  use 4
  intro n
  induction' n with n hn
  · bound
  · ring_nf at hn ⊢
    have hdiff : 2 * n + 9 ≤ 2 ^ n * 16 := by
      have h := Pset8Ex1 n
      rewrite [(by ring_nf : 2 ^ (n + 4) = 2 ^ n * 16)] at h
      apply h
    linarith only [hdiff, hn]

-- Problem 3

/-- Prove the statement. -/
example (n : ℕ) : ∃ k, n * (n + 1) * (2 * n + 1) = 6 * k := by
  induction' n with n hn
  · use 0
  · choose k hk using hn
    use k + (n + 1) ^ 2
    ring_nf at hk ⊢
    rewrite [← hk]
    ring_nf

-- Problem 4

/-- Theorem `SubseqGe`: Prove the statement. -/
theorem SubseqGe {σ : ℕ → ℕ} (hσ : ∀ i j, i < j → σ i < σ j) : ∀ n, n ≤ σ n := by
  intro n
  induction' n with n hn
  · bound
  · have hσn : σ n < σ (n + 1) := hσ n (n + 1) (by bound)
    bound

end RealAnalysisStory
