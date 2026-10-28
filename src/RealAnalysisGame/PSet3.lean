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

-- Problem 1

/-- Prove the full Archimedean Property. -/
example (x y : ℝ) (x_pos : 0 < x) (_y_pos : 0 < y) : ∃ N : ℕ, y < x * N := by
  use ⌈y / x⌉₊ + 1
  push_cast
  have hceil : y / x ≤ (⌈y / x⌉₊ : ℝ) := by bound
  have hyp : y < x * (y / x + 1) := by field_simp; bound
  have hppc : x * (y / x + 1) ≤ x * (⌈y / x⌉₊ + 1) := by bound
  linarith only [hyp, hppc]

-- Problem 2

/-- Prove that the sequence `(n + 1) / n` has a limit `L` and determine what it is. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) : ∃ L, SeqLim a L := by
  use 1
  intro ε ε_pos
  use ⌈1 / ε⌉₊ + 1
  intro n hn
  rewrite [ha n]

  have hceil : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
  have hceil_n : ⌈1 / ε⌉₊ < (n : ℝ) := by exact_mod_cast hn
  have hinv_n : 1 / ε < (n : ℝ) := by
    linarith only [hceil, hceil_n]
  have hn_pos : (n : ℝ) > 0 := by
    have hinv_pos : 0 < 1 / ε := by bound
    linarith only [hinv_pos, hinv_n]

  field_simp
  norm_num
  field_simp

  have h1_εn : 1 < ε * (n : ℝ) := by
    field_simp at hinv_n
    apply hinv_n
  linarith only [h1_εn]

-- Problem 3

/-- Determine what the limit of the sequence `1 / n^2` is, and prove it. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n^2) : ∃ L, SeqLim a L := by
  use 0
  intro ε ε_pos
  use ⌈1 / ε⌉₊ + 1
  intro n hn
  rewrite [ha n]

  have hceil : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
  have hceil_n : ⌈1 / ε⌉₊ < (n : ℝ) := by exact_mod_cast hn
  have hinv_n : 1 / ε < (n : ℝ) := by
    linarith only [hceil, hceil_n]
  have hn_pos : (n : ℝ) > 0 := by
    have hinv_pos : 0 < 1 / ε := by bound
    linarith only [hinv_pos, hinv_n]

  field_simp
  norm_num
  field_simp

  have h1_εn : 1 < ε * (n : ℝ) := by
    field_simp at hinv_n
    apply hinv_n

  have h1_n : 1 ≤ (n : ℝ) := by bound
  have h1_εn2' : 1 < ε * (n : ℝ) * n := by bound
  have h1_εn2 : 1 < (n : ℝ)^2 * ε := by linarith only [h1_εn2']

  apply h1_εn2

-- Problem 4

/--
Determine the limit `L` of the sequence `a n = (3n + 8) / (2n + 5)`,
and prove that `a` indeed converges to `L`.
-/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + 8) / (2 * n + 5)) : ∃ L, SeqLim a L := by
  use 3/2
  intro ε ε_pos
  let N := 1/4 * (1 / ε - 10)
  use ⌈N⌉₊ + 1
  intro n hn
  rewrite [ha n]

  have hden_pos : 0 < 2 * (n : ℝ) + 5 := by bound
  field_simp
  ring_nf
  rewrite [abs_of_nonneg (by bound)]
  field_simp

  have hceil : N ≤ ⌈N⌉₊ := by bound
  have hceil_n : ⌈N⌉₊ < (n : ℝ) := by exact_mod_cast hn
  have hNn : N < (n : ℝ) := by linarith only [hceil_n, hceil]
  dsimp [N] at hNn
  field_simp at hNn

  linarith only [hNn]

end RealAnalysisStory
