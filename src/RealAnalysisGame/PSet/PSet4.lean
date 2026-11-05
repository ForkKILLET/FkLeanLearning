/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Prove that this sequence diverges. -/
example (a : ℕ → ℝ)
    (ha2n : ∀ n, a (2 * n) = 3 - 1 / n) (ha2np1 : ∀ n, a (2 * n + 1) = 1 + 1 / n) :
    ¬ SeqConv a := by
  intro hconv
  choose l hl using hconv
  specialize hl (1/2) (by bound)
  choose N hN using hl

  have ⟨den, hden⟩ : ∃ den : ℕ, den = 2 * (N + 1) := by use 2 * (N + 1)

  have heven : |3 - 1 / den - l| < 1/2 := by
    specialize hN (2 * den) (by bound)
    rewrite [ha2n] at hN
    apply hN

  have hodd : |-1 - 1 / den + l| < 1/2 := by
    specialize hN (2 * den + 1) (by bound)
    rewrite [ha2np1] at hN
    have hneg : 1 + 1 / den - l = -(-1 - 1 / den + l) := by ring_nf
    rewrite [hneg, abs_neg] at hN
    apply hN

  have htriangle := by
    apply abs_add_le (3 - 1 / den - l) (-1 - 1 / den + l)
  ring_nf at htriangle

  have hsum : |3 - 1 / den - l| + |-1 - 1 / den + l| < 1 := by
    linarith only [heven, hodd]
  ring_nf at hsum

  have habs : |2 - (den : ℝ)⁻¹ * 2| < 1 := by
    linarith only [htriangle, hsum]

  rewrite [hden] at habs
  push_cast at habs
  norm_num at habs
  ring_nf at habs

  have hinv : (1 + (N : ℝ))⁻¹ ≤ 1 := by bound
  have hdiff : 2 - (1 + (N : ℝ))⁻¹ ≥ 1 := by bound
  rewrite [abs_of_nonneg (by bound)] at habs

  bound

end RealAnalysisStory
