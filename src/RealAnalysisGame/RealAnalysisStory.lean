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

-- Level 1: Introduction to Lean

/-- If we know that `x = 5`, then we can prove that `x = 5`. -/
example (x : ℝ) (h : x = 5) : x = 5 := by
  apply h

-- Level 2: The `rfl` tactic

/-- Every mathematical expression equals itself. -/
example (x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y := by
  rfl

-- Level 3: The `rewrite` tactic

/-- If we know that `x = 2`, then we can prove that `x + y = 2 + y`. -/
example (x y : ℝ) (h : x = 2) : x + y = 2 + y := by
  rewrite [h]
  rfl

-- Level 4: The `ring_nf` tactic

/-- The binomial expansion: `(x + y)^3 = x^3 + 3x^2y + 3xy^2 + y^3`. -/
example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring_nf

-- Level 5: The `use` tactic

/-- There exists a real number that makes this binomial expansion work. -/
example (x y : ℝ) : ∃ c : ℝ, (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4 := by
  use 6
  ring_nf

-- Level 6: The `intro` tactic

/-- For all positive real numbers, this algebraic identity holds. -/
example : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  intro _ _
  rfl

-- Level 7: The `specialize` tactic

/-- If a function of `x` always equals `x^2`, then it equals `t^2` when evaluated at `t`. -/
example (t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f x = x^2) : f t = t^2 := by
  specialize hf t t_pos
  apply hf

-- Level 8: The `choose` tactic

/--
If there exists a point where `f` equals `2`,
then there exists a point where `f^2` equals `4`.
-/
example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  choose c hc using h
  use c
  rewrite [hc]
  ring_nf

-- Level 9: Big Boss: The Ultimate Tactic Challenge

/-- BIG BOSS LEVEL: This problem requires all the tactics you've learned! -/
example (f : ℝ → ℝ)
    (h_existential : ∃ a : ℝ, f a = 3)
    (h_universal : ∀ x > 0, f (x + 1) = f x + 9) :
    ∃ b : ℝ, ∀ y > 0, f (y + 1)^2 = (f y + (f b)^2)^2 := by
  choose a ha using h_existential
  use a
  intro y y_pos
  specialize h_universal y y_pos
  rewrite [ha, h_universal]
  ring_nf

end RealAnalysisStory
