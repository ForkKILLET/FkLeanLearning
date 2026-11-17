/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

theorem AntitoneSubseq_of_UnBddPeaks
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X]
    {a : ℕ → X} (ha : UnBddPeaks a) : ∃ σ, Subseq σ ∧ Antitone (a ∘ σ) := by
  change ∀ k, ∃ n > k, IsAPeak a n at ha
  choose τ hτ haτ using ha
  change ∀ k m, m > τ k → a m ≤ a (τ k) at haτ

  let σ n := τ^[n + 1] 0
  use σ

  split_ands
  · apply Subseq_of_succ
    intro n
    change τ^[n + 1] 0 < τ^[(n + 1) + 1] 0
    rewrite [← succ_iterate τ (n + 1)]
    apply hτ

  · apply Antitone_of_succ
    intro n
    change a (τ^[(n + 1) + 1] 0) ≤ a (τ^[n + 1] 0)
    rewrite [← succ_iterate τ (n + 1), ← succ_iterate τ n]
    apply haτ
    apply hτ

end RealAnalysisStory
