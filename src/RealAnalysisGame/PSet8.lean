/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Theorem `Pset8Ex1`: Prove the statement. -/
theorem Pset8Ex1 (n : ℕ) : 2 * n + 9 ≤ 2 ^ (n + 4) := by
  induction' n with d hd
  · bound
  · ring_nf at hd ⊢
    bound

-- Problem 2

/-- Prove the statement. -/
example : ∃ N, ∀ n, (n + N) ^ 2 ≤ 2 ^ (n + N) := by
  use 4
  intro n
  induction' n with d hd
  · bound
  · ring_nf at hd ⊢
    have hdiff : 2 * d + 9 ≤ 2 ^ d * 16 := by
      have h := Pset8Ex1 d
      rewrite [(by ring_nf : 2 ^ (d + 4) = 2 ^ d * 16)] at h
      apply h
    linarith only [hdiff, hd]

-- Problem 3

/-- Prove the statement. -/
example (n : ℕ) : ∃ k, n * (n + 1) * (2 * n + 1) = 6 * k := by
  induction' n with d hd
  · use 0
  · choose k hk using hd
    use k + (d + 1) ^ 2
    ring_nf at hk ⊢
    rewrite [← hk]
    ring_nf

-- Problem 4

/-- Theorem `SubseqGe`: Prove the statement. -/
theorem SubseqGe {σ : ℕ → ℕ} (hσ : ∀ i j, i < j → σ i < σ j) : ∀ n, n ≤ σ n := by
  intro n
  induction' n with d hd
  · bound
  · have hσd : σ d < σ (d + 1) := hσ d (d + 1) (by bound)
    bound

end RealAnalysisStory
