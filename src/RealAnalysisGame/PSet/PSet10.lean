/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.MoreFunWithSequences
import RealAnalysisGame.AlgebraicLimitTheorem.PartIII
import RealAnalysisGame.AlgebraicLimitTheorem.PartIV
import RealAnalysisGame.AlgebraicLimitTheorem.PartV

set_option autoImplicit false

open Finset

namespace RealAnalysisStory

-- Problem 1

/-- Theorem `LimZeroTimesBdd`: Prove this -/
theorem LimZeroTimesBdd
    (a b c : ℕ → ℝ) (ha : SeqLim a 0) (hb : SeqBdd b) (hc : ∀ n, c n = a n * b n) : SeqLim c 0 := by
  let ⟨M, hM, hbM⟩ := hb
  intro ε ε_pos
  specialize ha (ε / M) (by bound)
  let ⟨N, han⟩ := ha

  use N
  intro n hn
  specialize han n (by bound)
  specialize hbM n
  rewrite [hc]
  ring_nf at han ⊢
  rewrite [abs_mul]

  have hmul_le : |a n| * |b n| ≤ |a n| * M := by bound
  have hmul_lt : |a n| * M < ε * M⁻¹ * M := by bound
  have hmul : |a n| * |b n| < ε * M⁻¹ * M := by linarith only [hmul_le, hmul_lt]
  field_simp at hmul
  apply hmul

-- Problem 2

/-- Theorem `ProdLim`: Prove this -/
theorem ProdLim
    (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M)
    (hc : ∀ n, c n = a n * b n) :
    SeqLim c (L * M) := by
  by_cases hL0 : L = 0
  · have hb_bdd := Bdd_of_Conv b M hb
    rewrite [hL0] at ha ⊢
    ring_nf
    apply LimZeroTimesBdd a b c ha hb_bdd hc
  · by_cases hM0 : M = 0
    · have ha_bdd := Bdd_of_Conv a L ha
      rewrite [hM0] at hb ⊢
      ring_nf
      have hc_comm : ∀ (n : ℕ), c n = b n * a n := by
        intro n
        rewrite [hc]
        ring_nf
      apply LimZeroTimesBdd b a c hb ha_bdd hc_comm
    · apply ProdLimNeNe a b c L M hL0 hM0 ha hb hc

-- Problem 3

/-- Theorem `OrderLimGt`: Prove this -/
theorem OrderLimGt (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : ∀ n, K < a n) : K ≤ L := by
  by_contra hKL
  have hKL : K > L := by bound

  specialize ha (K - L) (by bound)
  choose N hN using ha
  specialize hK N
  specialize hN N (by bound)

  apply abs_lt.1 at hN
  bound

-- Problem 4

/-- Prove this -/
example : ∃ a : ℕ → ℝ, SeqLim a 0 ∧ ∀ n, 0 < a n := by
  let a : ℕ → ℝ := fun n => 1 / (n + 1)
  use a
  split_ands
  · intro ε ε_pos
    let ⟨N, h1_εN⟩ := ArchProp ε_pos
    use N
    intro n hNn
    dsimp [a]
    norm_num
    field_simp at h1_εN ⊢
    rewrite [abs_of_nonneg (by bound)]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have hεN_εsn : ε * (N : ℝ) < ε * (n + 1) := by bound
    linarith only [h1_εN, hεN_εsn]
  · intro n
    dsimp [a]
    bound

-- Problem 5

/-- Prove this -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ SeqBdd a := by
  by_contra hbdd
  let ⟨M, hM, haM⟩ := hbdd
  specialize haM (⌈M⌉₊ + 1)
  rewrite [ha, abs_of_nonneg (by bound)] at haM
  push_cast at haM
  have hceil : M ≤ ⌈M⌉₊ := by bound
  bound

-- Problem 6

/-- Theorem `Diverge_of_DiffSubseqLim`: Prove this -/
theorem Diverge_of_DiffSubseqLim
    (a : ℕ → ℝ) (σ τ : ℕ → ℕ) (σsub : Subseq σ) (τsub : Subseq τ)
    (L M : ℝ) (hσ : SeqLim (a ∘ σ) L) (hτ : SeqLim (a ∘ τ) M) (hLM : L ≠ M) :
    ¬ SeqConv a := by
  by_contra ha
  let ⟨K, haK⟩ := ha
  have hσK := SubseqConv a K haK σ σsub
  have hLK : L = K := LimUnique (a ∘ σ) L K hσ hσK
  have hτK := SubseqConv a K haK τ τsub
  have hMK : M = K := LimUnique (a ∘ τ) M K hτ hτK
  bound

end RealAnalysisStory
