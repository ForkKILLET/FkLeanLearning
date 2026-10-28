/-
Adapted from Alex Kontorovich's RealAnalysisGame (Apache-2.0).
https://github.com/AlexKontorovich/RealAnalysisGame
Modified for this learning project; proofs written and adjusted locally.
See LICENSES/RealAnalysisGame-Apache-2.0.txt at the repository root.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF

import RealAnalysisGame.Prelude
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: The Convergence of a Sequence

/--
Theorem `ConstLim`:
Prove that the constant sequence converges to its constant value.
This is the Machinist's dream scenario: we're already producing exactly what's required!
-/
theorem ConstLim (a : ℕ → ℝ) (L : ℝ) (a_const : ∀ n, a n = L) : SeqLim a L := by
  intro ε ε_pos
  use 0
  intro n _
  rewrite [a_const]
  ring_nf
  norm_num
  apply ε_pos

end RealAnalysisStory
