/-
Adapted from Alex Kontorovich's RealAnalysisGame (Apache-2.0).
https://github.com/AlexKontorovich/RealAnalysisGame
Modified for this learning project; proofs written and adjusted locally.
See LICENSES/RealAnalysisGame-Apache-2.0.txt at the repository root.
-/
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

namespace RealAnalysisStory

/--
For a sequence `a : ℕ → ℝ` and a real number `L : ℝ`,
we say that `SeqLim a L` holds if: for every `ε > 0`,
there exists `N : ℕ` such that for all `n ≥ N`, we have `|a n - L| < ε`.
-/
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

end RealAnalysisStory
