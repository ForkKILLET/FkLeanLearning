/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.AlgebraicLimitTheorem.PartIV
import RealAnalysisGame.PSet.PSet8

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Big Boss: Product of Sequences

/-- Theorem `ProdLimNeNe`: Prove this -/
theorem ProdLimNeNe
    (a b c : ℕ → ℝ) (L M : ℝ) (hL : L ≠ 0) (_hM : M ≠ 0) (ha : SeqLim a L) (hb : SeqLim b M)
    (hc : ∀ n, c n = a n * b n) : SeqLim c (L * M) := by
  have ⟨B, hB, hbB⟩ := Bdd_of_Conv b M hb

  intro ε ε_pos
  let ε' := ε / (B + |L|)
  have Labs_pos := abs_pos.2 hL
  have ε'_pos : 0 < ε' := by bound

  specialize ha ε' ε'_pos
  specialize hb ε' ε'_pos
  choose Na hNa using ha
  choose Nb hNb using hb
  use Na + Nb
  intro n hn
  specialize hNa n (by bound)
  specialize hNb n (by bound)
  specialize hbB n

  rewrite [hc]
  rewrite [(by ring_nf : a n * b n - L * M = (a n - L) * b n + L * (b n - M))]
  have htri := abs_add_le ((a n - L) * b n) (L * (b n - M))
  have hsum : |(a n - L) * b n| + |L * (b n - M)| < ε := by
    rewrite [abs_mul, abs_mul]
    have hleft : |a n - L| * |b n| ≤ ε' * B := by bound
    have hright : |L| * |b n - M| < |L| * ε' := by bound
    have hsum : |a n - L| * |b n| + |L| * |b n - M| < ε' * (B + |L|) := by bound
    dsimp [ε'] at hsum
    field_simp at hsum
    apply hsum
  linarith only [htri, hsum]

-- Level 2: Order Limit Theorem

/-- Theorem `OrderLimLe`: Prove this -/
theorem OrderLimLe
    (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : SeqBddBy a K) : L ≤ K := by
  by_contra hLK
  have hLK : L > K := by bound

  specialize ha (L - K) (by bound)
  choose N hN using ha
  specialize hK N
  specialize hN N (by bound)

  apply abs_lt.1 at hN
  bound

-- Level 3: Subsequences

/-- Theorem `SubseqConv`: Prove this -/
theorem SubseqConv
    (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (σ : ℕ → ℕ) (hσ : Subseq σ) : SeqLim (a ∘ σ) L := by
  intro ε ε_pos
  specialize ha ε ε_pos
  choose N hN using ha
  use N
  intro n hn
  have hσn : σ n ≥ n := by apply SubseqGe hσ
  specialize hN (σ n) (by bound)
  apply hN

-- Level 4: Subsequence Example

/-- Prove this -/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ∃ σ L, Subseq σ ∧ SeqLim (a ∘ σ) L := by
  use (2 * ·)
  use 1
  split_ands
  · intro i j hij
    bound
  · intro ε ε_pos
    use 0
    dsimp
    intro n hn
    rewrite [ha]
    norm_num
    bound

end RealAnalysisStory
