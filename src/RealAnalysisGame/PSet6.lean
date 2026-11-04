/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.AlgebraicLimitTheorem.PartII

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

/-- Prove the statement. -/
example (x y z : ℝ) (hx : x = 2) (hy : y = 3) (hz : z = 4) : x = 2 ∧ y = 3 ∧ z = 4 := by
  split_ands
  · apply hx
  · apply hy
  · apply hz

-- Problem 2

/-- Prove the statement. -/
example (x y z : ℝ) (h : x = 2 ∧ y = 3 ∧ z = 4) : z = 4 := by
  apply h.2.2

-- Problem 3

/-- Prove the statement. -/
example (a : ℕ → ℝ) (ha : SeqLim a 5) : ∃ N, ∀ n ≥ N, 0 < a n := by
  specialize ha 1 (by bound)
  choose N hN using ha

  use N
  intro n hn
  specialize hN n (by bound)
  apply abs_lt.1 at hN
  linarith only [hN.1]

-- Problem 4

/-- Prove the statement. -/
proofs (a : ℕ → ℝ) (ha : ∀ N, ∃ n ≥ N, |a n| > 10) : ¬ ∃ L, |L| < 5 ∧ SeqLim a L where

  | lt_abs := by
    intro ⟨L, hL, hlim⟩
    specialize hlim 1 (by bound)
    choose N hN using hlim
    specialize ha N
    choose n hn using ha

    apply abs_lt.1 at hL

    specialize hN n hn.1
    apply abs_lt.1 at hN

    have han := hn.2
    apply lt_abs.1 at han
    cases' han with han_pos han_neg
    · linarith only [han_pos, hN.2, hL.2]
    · linarith only [han_neg, hN.1, hL.1]

  | no_lt_abs := by
    intro ⟨L, hL, hlim⟩
    specialize hlim 1 (by bound)
    choose N hN using hlim
    specialize ha N
    choose n hn using ha

    apply abs_lt.1 at hL

    specialize hN n hn.1
    apply abs_lt.1 at hN

    have habs : |a n| < 6 := by
      apply abs_lt.2
      split_ands
      · linarith only [hN.1, hL.1]
      · linarith only [hN.2, hL.2]

    bound

-- Problem 5

/-- Prove the statement. -/
example (a b c d e : ℕ → ℝ) (L : ℝ)
    (ha : SeqLim a L) (hc : SeqLim c L) (he : SeqLim e L)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) (hcd : ∀ n, c n ≤ d n) (hde : ∀ n, d n ≤ e n) :
    SeqLim b L ∧ SeqLim d L := by
  split_ands
  · apply SqueezeThm a b c L ha hc hab hbc
  · apply SqueezeThm c d e L hc he hcd hde

end RealAnalysisStory
