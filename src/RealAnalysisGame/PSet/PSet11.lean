/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.PSet.PSet8

set_option autoImplicit false

open Finset

namespace RealAnalysisStory

-- Problem 1

/-- Prove this -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ ∃ σ, Subseq σ ∧ SeqConv (a ∘ σ) := by
  by_contra ⟨σ, hσ, L, haσ⟩
  specialize haσ 1 (by bound)
  let ⟨N, haσ⟩ := haσ

  let n := N + ⌈L⌉₊ + 1 + 1
  have hNn : N ≤ n := by dsimp [n]; bound
  specialize haσ n hNn
  change |a (σ n) - L| < 1 at haσ
  rewrite [ha] at haσ
  apply abs_lt.1 at haσ

  have hσn : (n : ℝ) ≤ σ n := by exact_mod_cast SubseqGe hσ n
  have hLceil : L ≤ ⌈L⌉₊ := by bound
  have hLn : n - L > 1 := by dsimp [n]; push_cast; bound
  bound

end RealAnalysisStory
