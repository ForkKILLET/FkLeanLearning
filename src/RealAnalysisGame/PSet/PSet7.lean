/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Theorem `EventuallyBdd_of_SeqConv`: Prove the statement. -/
theorem EventuallyBdd_of_SeqConv
    (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) :
    ∃ N, ∀ n ≥ N, |a n| ≤ 2 * |L| := by
  have Labs_pos := abs_pos.2 hL
  specialize ha |L| (by bound)
  choose N hN using ha
  use N

  intro n hn
  specialize hN n hn

  have htri := abs_add_le (a n - L) L
  ring_nf at htri
  linarith only [htri, hN]

-- Problem 2

/-- Prove the statement. -/
example
    (a b : ℕ → ℝ) (L M : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b M) (hLM : L < M) :
    ∃ N, ∀ n ≥ N, a n < b n := by
  specialize ha ((M - L) / 2) (by bound)
  specialize hb ((M - L) / 2) (by bound)
  choose Na hNa using ha
  choose Nb hNb using hb
  use Na + Nb
  intro n hn
  specialize hNa n (by bound)
  specialize hNb n (by bound)

  apply abs_lt.1 at hNa
  apply abs_lt.1 at hNb
  have hanm : a n < (M + L) / 2 := by linarith only [hNa.2]
  have hbnm : b n > (M + L) / 2 := by linarith only [hNb.1]
  bound

-- Problem 3

/-- Prove the statement. -/
proofs (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| where

  | cases := by
    have abs_of_neg' {a : ℝ} (ha : a < 0) : |a| = -a := by
      rewrite [← abs_neg]
      apply abs_of_nonneg
      bound

    by_cases hx : x ≥ 0 <;> by_cases hy : y ≥ 0
    · rewrite [abs_of_nonneg hx, abs_of_nonneg hy]
      bound
    · have hy' : y < 0 := by bound
      have htri := abs_add_le x y
      rewrite [abs_of_nonneg hx, abs_of_neg' hy'] at htri ⊢
      rewrite [abs_of_nonneg (by bound : x - y ≥ 0)]
      ring_nf at htri ⊢
      apply htri
    · have hx' : x < 0 := by bound
      have htri := abs_add_le x y
      rewrite [abs_of_neg' hx', abs_of_nonneg hy] at htri ⊢
      rewrite [(by ring_nf : -x - y = -(x + y)), abs_neg]
      rewrite [(by ring_nf : x - y = -(-x + y)), abs_neg]
      rewrite [abs_of_nonneg (by bound : -x + y ≥ 0)]
      apply htri
    · have hx' : x < 0 := by bound
      have hy' : y < 0 := by bound
      rewrite [abs_of_neg' hx', abs_of_neg' hy']
      rewrite [(by ring_nf : -x - -y = -(x - y)), abs_neg]
      bound

  | theorem' := by apply abs_abs_sub_abs_le

end RealAnalysisStory
