/- Adapted from RealAnalysisGame; see the repository README.md for attribution and modification details. -/

import RealAnalysisGame.Prelude

set_option autoImplicit false

namespace RealAnalysisStory

-- Level 1: Iterated Subsequence

/-- Theorem `Subseq_of_Iterate` -/
theorem Subseq_of_Iterate
    (σ : ℕ → ℕ) (hσ : ∀ n, n < σ n) (n₀ : ℕ) : Subseq (fun n => σ^[n] n₀) := by
  apply subseq_of_succ
  intro n
  rewrite [← succ_iterate]
  apply hσ

-- Level 2: Enhanced Choose

proofs (p : ℕ → Prop) (h : ∀ N, ∃ n > N, p n) : ∃ σ, Subseq σ ∧ ∀ n, p (σ n) where

  | induction := by
    let σ (n : ℕ) : ℕ := by
      induction' n with k σk
      · apply (h 0).choose
      · apply (h σk).choose
    use σ
    split_ands
    · apply subseq_of_succ
      intro n
      apply (h (σ n)).choose_spec.1
    · intro n
      cases' n with k
      · apply (h 0).choose_spec.2
      · apply (h (σ k)).choose_spec.2

  | Nat.rec :=
    let σ : ℕ → ℕ := Nat.rec
      (h 0).choose
      fun _ σk => (h σk).choose
    ⟨ σ
    , subseq_of_succ σ fun n => (h (σ n)).choose_spec.1
    , fun
      | 0 => (h 0).choose_spec.2
      | .succ k => (h (σ k)).choose_spec.2
    ⟩

  | choose := by
    choose τ hτN hτp using h
    use fun n => τ^[n + 1] 0
    split_ands
    · apply Subseq_of_Iterate
      apply hτN
    · intro n
      change p (τ^[n + 1] 0)
      rewrite [← succ_iterate]
      apply hτp

-- Level 3: Monotone and Bounded Implies Cauchy

/-- Lemma `IterateGap` -/
lemma IterateGap
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X]
    {a : ℕ → X} {τ σ : ℕ → ℕ} {ε : X}
    (ha : Monotone a) (hτ : ∀ n, τ n ≥ n) (hσ : ∀ n, σ n ≥ τ n)
    (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|) :
    ∀ (k : ℕ), k * ε ≤ a (σ^[k] 0) - a 0 := by
  intro k
  induction' k with k hk
  · norm_num
  · push_cast
    have hδ : ε ≤ a (σ^[k + 1] 0) - a (σ^[k] 0) := by
      rewrite [← succ_iterate]
      specialize hgap (σ^[k] 0)
      have ha_τσ : a (τ (σ^[k] 0)) ≤ a (σ (σ^[k] 0)) := by
        apply ha
        apply hσ
      rewrite [abs_of_nonneg (by bound)] at hgap
      have ha_1τ : a (σ^[k] 0) ≤ a (τ (σ^[k] 0)) := by
        apply ha
        apply hτ
      linarith only [hgap, ha_1τ]
    linarith only [hk, hδ]

/-- Theorem `IsCauchy_of_MonotoneBdd` -/
theorem IsCauchy_of_MonotoneBdd
    {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X]
    {a : ℕ → X} {M : X} (ha : Monotone a) (hM : ∀ n, a n ≤ M) : IsCauchy a := by
  intro ε ε_pos
  by_contra hN
  push_neg at hN
  choose τ h1τ σ hτσ hgap using hN
  let k := (M + 1 - a 0) / ε
  have hdiff : ⌈k⌉₊ * ε ≤ a (σ^[⌈k⌉₊] 0) - a 0 := IterateGap ha h1τ hτσ hgap ⌈k⌉₊
  have hceil : k ≤ ⌈k⌉₊ := by bound
  have hmul : k * ε ≤ ⌈k⌉₊ * ε := by bound
  have hdiff : k * ε ≤ a (σ^[⌈k⌉₊] 0) - a 0 := by bound
  have hkε : k * ε = M + 1 - a 0 := by dsimp [k]; field_simp
  rewrite [hkε] at hdiff
  linarith only [hdiff, hM (σ^[⌈k⌉₊] 0)]

end RealAnalysisStory
