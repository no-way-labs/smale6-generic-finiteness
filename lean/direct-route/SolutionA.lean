import DirectRoute.LemmaA

/-!
The statements of `ChallengeA.lean` with their proofs. The definitions are in `DirectRoute/DefsA.lean`.
-/

open Finset

/-- Lemma A: at a solution of N_n with nonzero masses over a valued field, the weights form a weight
datum. -/
theorem lemmaA {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) : (weights v n m X Y).IsWeightDatum := lemmaA_proof v n hn m X Y Pf hm hsol

/-- A corollary that joins the two halves: at a solution over a valued field whose mass weights lie in
W_n(τ), τ ≥ 2n², the valuation of every (X_t − X_l)(Y_t − Y_l) is bounded above in terms of the mass
weights alone. This is the hypothesis of Proposition D2 in Theorem D5′. -/
theorem solution_bound {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) (τ : ℝ) (hτ : 2 * (n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber n τ fun t => (v (m t)).untopD 0) (t l : ℕ) (htl : t < l) (hl : l < n) :
    v ((X t - X l) * (Y t - Y l))
      ≤ ((2 * (2 * (n : ℝ) - 1) * (∑ j ∈ range n, |(v (m j)).untopD 0|) / 3
          + 2 * (v (m t)).untopD 0 + 2 * (v (m l)).untopD 0 : ℝ) : WithTop ℝ) := solution_bound_proof v n hn m X Y Pf hm hsol τ hτ hu t l htl hl
