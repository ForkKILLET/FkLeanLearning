/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Monotone Subsequence

lemma monotone_nat_of_le_succ'
    {X : Type*} [LinearOrder X] [NormedField X] [IsStrictOrderedRing X]
    {a : ℕ → X} (ha : ∀ n, a n ≤ a (n + 1)) : Monotone a := by
  intro m n hmn
  induction' n with n ih
  · have hm : m = 0 := by bound
    bound
  · by_cases hm : m ≤ n
    · specialize ih hm
      specialize ha n
      linarith only [ha, ih]
    · have hm : m = n + 1 := by bound
      bound

/-- Theorem `MonotoneSubseq_of_BddPeaks` -/
theorem MonotoneSubseq_of_BddPeaks
    {X : Type*} [LinearOrder X] [NormedField X] [IsStrictOrderedRing X]
    {a : ℕ → X} (ha : ¬ UnBddPeaks a) : ∃ σ, Subseq σ ∧ Monotone (a ∘ σ) := by
  change ¬∀ k, ∃ n > k, ∀ m > n, a m ≤ a n at ha
  push_neg at ha
  let ⟨k, hak⟩ := ha
  choose τ' hτ' haτ' using hak

  let τ n := if hnk : n > k then τ' n hnk else k + 1
  let σ n := τ^[n] (k + 1)
  use σ

  have hτidk : ∀ n, n < τ n ∧ k < τ n := by
    intro n
    change
      ( n < (if hnk : n > k then τ' n hnk else k + 1)
      ∧ k < (if hnk : n > k then τ' n hnk else k + 1)
      )
    by_cases hnk : n > k
    · specialize hτ' n hnk
      bound
    · bound
  let hτ n := (hτidk n).1
  let hτk n := (hτidk n).2

  have haτ : ∀ n, n > k → a n ≤ a (τ n) := by
    intro n hnk
    change a n ≤ a (if hnk : n > k then τ' n hnk else k + 1)
    specialize haτ' n hnk
    bound

  split_ands
  · apply Subseq_of_succ
    intro n
    change τ^[n] (k + 1) < τ^[n + 1] (k + 1)
    rewrite [← succ_iterate]
    specialize hτ (τ^[n] (k + 1))
    apply hτ

  · apply Monotone_of_succ
    intro n
    change a (τ^[n] (k + 1)) ≤ a (τ^[n + 1] (k + 1))
    rewrite [← succ_iterate]
    apply haτ
    cases' n with n
    · change k + 1 > k
      bound
    · rewrite [← succ_iterate]
      apply hτk

end RealAnalysisStory
