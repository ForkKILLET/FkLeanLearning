/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Doubling a Convergent Sequence

/--
Prove that constant multiples of convergent sequences
converge to the constant multiple of the limit.
This is the Machinist's response to scaling demands:
'If you want double the output with the same tolerance,
I need half the tolerance on the original process!'
-/
example (a b : ℕ → ℝ) (L : ℝ) (h : SeqLim a L) (b_scaled : ∀ n, b n = 2 * a n) :
    SeqLim b (2 * L) := by
  intro ε ε_pos
  specialize h (ε / 2) (by bound)
  choose N hN using h
  use N
  intro n hn
  specialize hN n hn

  rewrite [b_scaled]
  have hmul : 2 * a n - 2 * L = 2 * (a n - L) := by ring_nf
  rewrite [hmul, abs_mul]
  norm_num

  bound

end RealAnalysisStory
