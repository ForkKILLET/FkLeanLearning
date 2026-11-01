/-
Adapted from Alex Kontorovich's RealAnalysisGame (Apache-2.0).
https://github.com/AlexKontorovich/RealAnalysisGame
Modified for this learning project; proofs written and adjusted locally.
See LICENSES/RealAnalysisGame-Apache-2.0.txt at the repository root.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Bound
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Group.Abs

import RealAnalysisGame.Prelude
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: NonConvergence

/-- Prove that the sequence `1, -1, 1, -1,...` diverges. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ¬ SeqConv a := by
  intro hconv
  choose l hl using hconv
  specialize hl (1/2) (by bound)
  choose N hN using hl

  have heven : |1 - l| < 1/2 := by
    specialize hN (2 * N) (by bound)
    rewrite [ha] at hN
    norm_num at hN
    apply hN

  have hodd : |l + 1| < 1/2 := by
    specialize hN (2 * N + 1) (by bound)
    rewrite [ha] at hN
    ring_nf at hN
    norm_num at hN
    have hneg : -l - 1 = -(l + 1) := by ring_nf
    rewrite [hneg, abs_neg] at hN
    apply hN

  have htriangle : |(1 - l) + (l + 1)| ≤ |1 - l| + |l + 1| := by
    apply abs_add_le
  ring_nf at htriangle
  norm_num at htriangle

  have hsum : |1 - l| + |l + 1| < 1 := by
    linarith only [heven, hodd]
  ring_nf at hsum

  bound

end RealAnalysisStory
