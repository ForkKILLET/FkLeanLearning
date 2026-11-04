/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: NotEven

/-- Theorem `IdLeTwoPow`: Prove this -/
proofs IdLeTwoPow (n : ℕ) : n < 2 ^ n where

  | by_cases := by
    induction' n with k hk
    · bound
    · by_cases hk0 : k = 0
      · rewrite [hk0]
        bound
      · ring_nf
        linarith only [ge_one_of_nonzero hk0, hk]

  | linarith := by
    induction' n with k hk
    · bound
    · ring_nf
      linarith only [hk]

end RealAnalysisStory
