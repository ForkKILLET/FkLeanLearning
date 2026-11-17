/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.PSet.PSet12
import RealAnalysisGame.PSet.PSet13
import RealAnalysisGame.MonotoneSubsequence

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

theorem BolzanoWeierstrass
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X]
    (a : ℕ → X) (ha : SeqBdd a) : ∃ σ, Subseq σ ∧ IsCauchy (a ∘ σ) := by
  let ⟨M, hM, haM⟩ := ha
  by_cases hpeaks : UnBddPeaks a
  · let ⟨σ, hσ, haσ⟩ := AntitoneSubseq_of_UnBddPeaks hpeaks
    use σ
    split_ands
    · apply hσ
    · have haσM : ∀ n, -M ≤ (a ∘ σ) n := by
        intro n
        specialize haM (σ n)
        apply abs_le.1 at haM
        bound
      apply IsCauchy_of_AntitoneBdd haσ haσM
  · let ⟨σ, hσ, haσ⟩ := MonotoneSubseq_of_BddPeaks hpeaks
    use σ
    split_ands
    · apply hσ
    · have haσM : ∀ n, (a ∘ σ) n ≤ M := by
        intro n
        specialize haM (σ n)
        apply abs_le.1 at haM
        bound
      apply IsCauchy_of_MonotoneBdd haσ haσM

end RealAnalysisStory
