/-
Adapted from Alex Kontorovich's RealAnalysisGame (Apache-2.0).
https://github.com/AlexKontorovich/RealAnalysisGame
Modified for this learning project; proofs written and adjusted locally.
See LICENSES/RealAnalysisGame-Apache-2.0.txt at the repository root.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Group.Abs

import RealAnalysisGame.Prelude
import MultiProof

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Big Boss: The Sum of Convergent Sequences

/--
Theorem `SumLim`:
Prove that the sum of two convergent sequences converges to the sum of their limits.
This is the mathematician's version of
'if two factories each meet their quality standards, their combined output will too!'
-/
theorem SumLim (a b c : ℕ → ℝ) (L M : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n + b n) :
    SeqLim c (L + M) := by
  intro ε ε_pos
  specialize ha (ε / 2) (by bound)
  choose Na hNa using ha
  specialize hb (ε / 2) (by bound)
  choose Nb hNb using hb
  use Na + Nb

  intro n hn
  rewrite [hc n]
  have hsum : |a n + b n - (L + M)| = |(a n - L) + (b n - M)| := by ring_nf
  rewrite [hsum]

  have htri := abs_add_le (a n - L) (b n - M)
  linarith only [htri, hNa n (by bound), hNb n (by bound)]

-- Level 2: Split Ands

/-- Prove this -/
example (x y : ℝ) (hx : x = 2) (hy : y = 3) : x = 2 ∧ y = 3 := by
  split_ands
  · apply hx
  · apply hy

-- Level 3: Left and Right

/-- Prove this -/
example (x y : ℝ) (_hx : x = 2) (hy : y = 3) : x = 3 ∨ y = 3 := by
  right
  apply hy

-- Level 4: Dot Notation

/-- Prove this -/
example (x y : ℝ) (h : x = 2 ∧ y = 3) : y = 3 := by
  apply h.2

-- Level 5: Cases'

/-- Prove this -/
example (x y : ℝ) (h : x = 2 ∨ y = 3) : (x - 2) * (y - 3) = 0 := by
  cases' h with h1 h2
  · rewrite [h1]
    ring_nf
  · rewrite [h2]
    ring_nf

-- Level 6: AbsLe

/-- Prove this -/
example (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) : ∃ N, ∀ n ≥ N, a n ≥ L - 1 := by
  specialize ha 1 (by bound)
  choose N hN using ha
  use N
  intro n hn
  specialize hN n hn
  apply abs_lt.1 at hN
  linarith only [hN.1]

-- Level 7: Big Boss : Squeeze Theorem

/-- Theorem `SqueezeThm`: Prove this -/
theorem SqueezeThm (a b c : ℕ → ℝ) (L : ℝ)
    (aToL : SeqLim a L) (cToL : SeqLim c L)
    (aLeb : ∀ n, a n ≤ b n) (bLec : ∀ n, b n ≤ c n) :
    SeqLim b L := by
  intro ε ε_pos
  specialize aToL ε ε_pos
  specialize cToL ε ε_pos
  choose Na hNa using aToL
  choose Nc hNc using cToL
  use Na + Nc
  intro n hn
  specialize hNa n (by bound)
  specialize hNc n (by bound)
  apply abs_lt.1 at hNa
  apply abs_lt.1 at hNc
  specialize aLeb n
  specialize bLec n

  apply abs_lt.2
  split_ands
  · linarith only [hNa.1, aLeb]
  · linarith only [hNc.2, bLec]

end RealAnalysisStory
