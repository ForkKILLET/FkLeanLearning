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

import RealAnalysisGame.Prelude
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Archimedean Property

/--
Theorem `ArchProp`:
Prove the "Archimedean Property" that no matter how small `ε > 0` may be,
there is always a natural number `N` with `1 / ε < N`.
-/
theorem ArchProp {ε : ℝ} (_hε : 0 < ε) : ∃ N : ℕ, 1 / ε < N := by
  use ⌈1 / ε⌉₊ + 1
  have h : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
  push_cast
  bound

-- Level 2: First Real Limit

/--
Theorem `OneOverNLimZero`:
Prove that the sequence `a n = 1 / n` converges to `0`.
This is our first substantive limit proof, requiring the Archimedean Property.
-/
theorem OneOverNLimZero (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : SeqLim a 0 := by
  intro ε ε_pos
  have ⟨N, hεN⟩ := ArchProp ε_pos
  use N

  intro n hnN'
  rewrite [ha n]
  norm_num

  have hNn : N ≤ (n : ℝ) := by exact_mod_cast hnN'
  have inv_ε_pos : 1 / ε > 0 := by bound
  have n_pos : (n : ℝ) > 0 := by linarith only [inv_ε_pos, hεN, hNn]
  field_simp
  field_simp at hεN

  have hεNεn : ε * N ≤ ε * (n : ℝ) := by bound
  linarith only [hεN, hεNεn]

end RealAnalysisStory
