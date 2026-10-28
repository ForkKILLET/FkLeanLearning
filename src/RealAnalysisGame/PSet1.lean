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

/--
Given that `f u = 2 * u + 1` for all `u`,
prove that there exists some a such that `f 3 = a`.
-/
example (f : ℝ → ℝ) (h : ∀ u, f u = 2 * u + 1) : ∃ a, f 3 = a := by
  specialize h 3
  ring_nf at h
  use 7

-- Problem 2

/--
Show that there exists a constant `c` so that,
for any real numbers `x` and `y` with `x^2 + y^2 = 2` and `x * y = 1`,
we have `(x + y) ^ 2 = c`.
-/
example : ∃ c, ∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y = 1 → (x + y) ^ 2 = c := by
  use 4
  intro x y h1 h2
  have hxy : (x + y)^2 = x^2 + y^2 + 2 * (x * y) := by ring_nf
  rewrite [hxy, h1, h2]
  ring_nf

-- Problem 3

/-- Solve the problem -/
proofs (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g x + 3) (h2 : g 0 = 5) : g 1 = 8 where

  | to_left := by
    have hs1 : (1 : ℝ) = 0 + 1 := by ring_nf
    rewrite [hs1, h1, h2]
    ring_nf

  | to_right := by
    specialize h1 0
    rewrite [h2] at h1
    ring_nf at h1
    apply h1

-- Problem 4

/-- Solve the problem -/
proofs (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g x + 3) (h2 : g 0 = 5) : g 2 = 11 where

  | to_left := by
    have hs2 : (2 : ℝ) = 1 + 1 := by ring_nf
    have hs1 : (1 : ℝ) = 0 + 1 := by ring_nf
    rewrite [hs2, h1, hs1, h1, h2]
    ring_nf

  | to_right := by
    have hg0 := h1 0
    ring_nf at hg0
    have hg1 := h1 1
    rewrite [hg0, h2] at hg1
    ring_nf at hg1
    apply hg1

-- Problem 5

/-- Solve the problem -/
example
    (p : ℝ → ℝ) (x : ℝ) (h1 : ∀ t, p t = t ^ 2 + 2 * t) (h2 : p x = 15) :
    ∃ b, x ^ 2 + 2 * x = b := by
  use 15
  specialize h1 x
  rewrite [← h1, h2]
  rfl

end RealAnalysisStory
