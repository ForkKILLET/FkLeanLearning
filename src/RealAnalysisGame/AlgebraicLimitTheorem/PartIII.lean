/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Uniqueness of Limits

/-- Theorem `LimUnique`: Prove that limits are unique. -/
theorem LimUnique (a : ℕ → ℝ) (L M : ℝ) (haL : SeqLim a L) (haM : SeqLim a M) : L = M := by
  by_contra hLM

  have hlim_diff : L - M ≠ 0 := by bound
  have hlim_abs : |L - M| > 0 := abs_pos_of_nonzero hlim_diff
  specialize haL (|L - M| / 2) (by bound)
  specialize haM (|L - M| / 2) (by bound)
  choose NL hNL using haL
  choose NM hNM using haM
  specialize hNL (NL + NM) (by bound)
  specialize hNM (NL + NM) (by bound)

  let an := a (NL + NM)
  rewrite [← abs_neg (an - L)] at hNL
  have htri := abs_add (-(an - L)) (an - M)
  ring_nf at htri
  have hsum : |-(an - L)| + |an - M| < |L - M| := by linarith only [hNL, hNM]
  ring_nf at hsum

  bound

-- Level 2: Eventually

/-- Theorem `EventuallyGeHalfLimPos` -/
theorem EventuallyGeHalfLimPos (a : ℕ → ℝ) (L : ℝ) (haL : SeqLim a L) (L_nonzero : L ≠ 0) :
    ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a n| := by
  have L_abs_pos : |L| > 0 := abs_pos_of_nonzero L_nonzero
  specialize haL (|L| / 2) (by bound)
  choose N hN using haL
  use N
  intro n hn
  specialize hN n (by bound)
  have htri := abs_add (a n) (L - a n)
  rewrite [← abs_neg (L - a n)] at htri
  ring_nf at htri
  linarith only [htri, hN]

-- Level 3: Sequences of Absolute Values

/-- Theorem `AbsLim` -/
theorem AbsLim
    (a : ℕ → ℝ) (L : ℝ) (haL : SeqLim a L) (b : ℕ → ℝ) (b_eq_aabs : ∀ n, b n = |a n|) :
    SeqLim b |L| := by
  intro ε ε_pos
  specialize haL ε ε_pos
  choose N hN using haL
  use N
  intro n hn
  specialize hN n hn
  rewrite [b_eq_aabs]
  have hsub := (abs_Lipschitz (x := a n) (y := L))
  linarith only [hsub, hN]

-- Level 4: SeqInvLim

/-- Theorem `InvLim` -/
theorem InvLim
    (a : ℕ → ℝ) (L : ℝ) (haL : SeqLim a L) (L_nonzero : L ≠ 0)
    (b : ℕ → ℝ) (b_eq_ainv : ∀ n, b n = 1 / a n) :
    SeqLim b (1 / L) := by
  intro ε ε_pos
  let ε' := |L| * |L| * ε / 2
  have Labs_pos := abs_pos_of_nonzero L_nonzero
  have han := EventuallyGeHalfLimPos a L haL L_nonzero

  specialize haL ε' (by bound)
  choose N hN using haL

  choose Nan hNan using han
  use N + Nan

  intro n hn
  specialize hN n (by bound)
  specialize hNan n (by bound)
  have an_ne0 : a n ≠ 0 := nonzero_of_abs_pos (by bound)

  rewrite [b_eq_ainv]
  have hnorm : 1 / a n - 1 / L = -(a n - L) / (L * a n) := by
    field_simp
    ring_nf
  rewrite [hnorm, abs_div, abs_neg, abs_mul]
  field_simp
  have hε' : ε' ≤ |L| * |a n| * ε := by
    dsimp [ε']
    rewrite [(by ring_nf : |L| * |L| * ε / 2 = |L| * (|L| / 2) * ε)]
    bound

  linarith only [hε', hN]

-- Level 5: ByCases

/--
Theorem `EventuallyGeHalfLim`:
Prove `EventuallyGeHalfLimPos`, but without the assumption that `L ≠ 0`.
-/
theorem EventuallyGeHalfLim
    (a : ℕ → ℝ) (L : ℝ) (haL : SeqLim a L) :
    ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a n| := by
  by_cases hL : L = 0
  · use 0
    intro n hn
    rewrite [hL]
    norm_num
  · apply EventuallyGeHalfLimPos a L haL hL

end RealAnalysisStory
