/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.AlgebraicLimitTheorem.PartIV

open Finset

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Big Boss : Limits are Cauchy

/-- Theorem `IsCauchy_of_SeqConv` -/
theorem IsCauchy_of_SeqConv {a : ℕ → ℝ} (ha : SeqConv a) : IsCauchy a := by
  intro ε ε_pos
  let ⟨L, haL⟩ := ha
  specialize haL (ε / 2) (by bound)
  let ⟨N, haL⟩ := haL
  use N

  intro n hn m hm
  have hanL := haL n (by bound)
  have hamL := haL m (by bound)
  have htri := abs_add (a m - L) (L - a n)
  ring_nf at htri
  rewrite [← abs_neg (L - a n)] at htri
  ring_nf at htri
  have hsum : |a m - L| + |a n - L| < ε := by bound
  linarith only [htri, hsum]

-- Level 2: Sums of Cauchy sequences

/-- Theorem `IsCauchy_of_Sum` -/
theorem IsCauchy_of_Sum {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X]
    (a b : ℕ → X) (ha : IsCauchy a) (hb : IsCauchy b) : IsCauchy (a + b) := by
  intro ε ε_pos
  specialize ha (ε / 2) (by bound)
  specialize hb (ε / 2) (by bound)
  let ⟨Na, ha⟩ := ha
  let ⟨Nb, hb⟩ := hb

  use Na + Nb
  intro n hn m hm
  change |(a m + b m) - (a n + b n)| < ε
  have htri := abs_add (a m - a n) (b m - b n)
  ring_nf at htri ⊢
  specialize ha n (by bound) m (by bound)
  specialize hb n (by bound) m (by bound)
  have hsum : |a m - a n| + |b m - b n| < ε := by bound
  linarith only [htri, hsum]

-- Level 3: Cauchy Implies Bounded

/-- Theorem `IsBdd_of_Cauchy` -/
theorem IsBdd_of_Cauchy {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X]
    (a : ℕ → X) (ha : IsCauchy a) : SeqBdd a := by
  let ⟨N, ha⟩ := ha 1 (by bound)
  use |a N| + ∑ i ∈ range N, |a i| + 1
  have habs_nonneg : 0 ≤ |a N| := by bound
  have hsum_nonneg : 0 ≤ ∑ i ∈ range N, |a i| := by
    apply sum_nonneg
    intro i hi
    bound

  split_ands
  · bound
  · intro n
    by_cases hnN : n < N
    · have hsum : |a n| ≤ ∑ i ∈ range N, |a i| := by
        apply TermLeSum
        apply hnN
      bound
    · have hnN : n ≥ N := by bound
      specialize ha N (by bound) n hnN
      have htri := abs_add (a n - a N) (a N)
      ring_nf at htri
      bound

end RealAnalysisStory
