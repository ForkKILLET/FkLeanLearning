/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: NotEven

/-- Theorem `IdLeTwoPow`: Prove this -/
proofs IdLeTwoPow (n : ℕ) : n < 2 ^ n where

  | by_cases := by
    induction' n with n hn
    · bound
    · by_cases hn0 : n = 0
      · rewrite [hn0]
        bound
      · ring_nf
        linarith only [ge_one_of_nonzero hn0, hn]

  | linarith := by
    induction' n with n hn
    · bound
    · ring_nf
      linarith only [hn]

end RealAnalysisStory
