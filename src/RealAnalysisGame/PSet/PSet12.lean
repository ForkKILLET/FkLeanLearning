/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude
import RealAnalysisGame.CauchySequences.PartII

set_option autoImplicit false

namespace RealAnalysisStory

-- Problem 1

theorem IsCauchy_of_AntitoneBdd
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X]
    {a : ℕ → X} {M : X} (ha : Antitone a) (hM : ∀ n, M ≤ a n) : IsCauchy a := by
  have ha' := MonotoneNeg_of_Antitone a ha
  have hM' : ∀ n, (-a) n ≤ -M := by
    intro n
    rewrite [show (-a) n = -a n by rfl]
    bound
  have ha_cauchy' := IsCauchy_of_MonotoneBdd ha' hM'
  have ha_cauchy := IsCauchyNeg (-a) ha_cauchy'
  rewrite [show - (-a) = a by ring_nf] at ha_cauchy
  apply ha_cauchy

-- Problem 2

example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a := by
  split_ands
  · let a' : ℕ → ℝ := fun n => a (n + 1)
    have a'_antitone : Antitone a' := by
      intro m n hmn
      dsimp [a']
      repeat rewrite [ha]
      field_simp
      push_cast
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast hmn
      bound
    have a'_bdd : ∀ n, 0 ≤ a' n := by
      intro n
      dsimp [a']
      rewrite [ha]
      bound
    have a'_cauchy := IsCauchy_of_AntitoneBdd a'_antitone a'_bdd

    intro ε ε_pos
    specialize a'_cauchy ε ε_pos
    let ⟨N, ha'⟩ := a'_cauchy
    use N + 1
    intro n hn m hm
    cases' n with n; bound
    cases' m with m; bound
    specialize ha' n (by bound) m (by bound)
    dsimp [a'] at ha'
    apply ha'

  · dsimp [Monotone]
    push_neg
    use 1, 2
    split_ands
    · norm_num
    · repeat rewrite [ha]
      norm_num

  · dsimp [Antitone]
    push_neg
    use 0, 1
    split_ands
    · norm_num
    · repeat rewrite [ha]
      norm_num

end RealAnalysisStory
