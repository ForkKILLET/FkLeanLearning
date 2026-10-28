/-
Adapted from Alex Kontorovich's RealAnalysisGame (Apache-2.0).
https://github.com/AlexKontorovich/RealAnalysisGame
Modified for this learning project; proofs written and adjusted locally.
See LICENSES/RealAnalysisGame-Apache-2.0.txt at the repository root.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF

import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Find the correct constant. -/
example : ∃ c, ∀ (x : ℝ),
    (1 + x / 2 - x^2 / 8 + x^3 / 16 - 5 * x^4 / 128 + c * x^5)^2 - (1 + x) =
    x^6 * (21 / 512 - 3 * x / 256 + 81 * x^2 / 16384 - 35 * x^3 / 16384 + 49 * x^4 / 65536) := by
  use 7/256
  intro x
  ring_nf

-- Problem 2

/-- Find the correct constant. -/
example : ∃ c d e, ∀ (x : ℝ),
    (1 + 3 * x / 2 + c * x^2 + d * x^3 + e * x^4)^2 - (1 + x)^3 =
    x^5 * (3/128 + (11 * x)/512 - (3 * x^2)/1024 + (9 * x^3)/16384 ) := by
  use 3/8, -1/16, 3/128
  intro x
  ring_nf

end RealAnalysisStory
