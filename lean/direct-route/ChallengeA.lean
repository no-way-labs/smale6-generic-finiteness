import Challenge

/-!
# Lemma A: the weights of a solution form a weight datum

Source: `docs/allN-direct-route-second-read.md` (the brief), §1 (the system N_n) and §2 (Lemma A).
This file uses the definitions of `Challenge.lean` (`Datum`, `Datum.IsWeightDatum`) without change.

The field `K` is any field with a valuation with values in `WithTop ℝ` (an additive valuation:
`v 0 = ⊤`, `v (x * y) = v x + v y`, `min (v x) (v y) ≤ v (x + y)`). The field of Hahn series of the brief
is one such field. The bodies are 0, …, n − 1; the functions `m`, `X`, `Y`, `Pf` are read at indices
below n only.

This file declares no notation, no instance and no attribute.
-/

open Finset

noncomputable section

/-- A solution of the system N_n (brief §1): P_tl = P_lt, and
(N1) P_tl² (X_t − X_l)(Y_t − Y_l) = 1, (N2) X_t = Σ_{l ≠ t} m_l P_tl³ (X_t − X_l), (N3) the same for Y. -/
structure IsSolution {K : Type} [Field K] (n : ℕ) (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) : Prop where
  psymm : ∀ t l, t < n → l < n → Pf t l = Pf l t
  n1 : ∀ t l, t < n → l < n → t ≠ l → Pf t l ^ 2 * (X t - X l) * (Y t - Y l) = 1
  n2 : ∀ t, t < n → X t = ∑ l ∈ (range n).erase t, m l * Pf t l ^ 3 * (X t - X l)
  n3 : ∀ t, t < n → Y t = ∑ l ∈ (range n).erase t, m l * Pf t l ^ 3 * (Y t - Y l)

/-- The weights of a solution (brief §2): u_t = v(m_t), ζ_tl = v(X_t − X_l), ω_tl = v(Y_t − Y_l),
ξ_t = v(X_t), η_t = v(Y_t). The real numbers are read off with `untopD 0`; for a solution with nonzero
masses the valuations in question are not ⊤. -/
def weights {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (m X Y : ℕ → K) : Datum where
  n := n
  u := fun t => (v (m t)).untopD 0
  z := fun t l => (v (X t - X l)).untopD 0
  w := fun t l => (v (Y t - Y l)).untopD 0
  xi := fun t => v (X t)
  eta := fun t => v (Y t)

/-- Lemma A: at a solution of N_n with nonzero masses over a valued field, the weights form a weight
datum. -/
theorem lemmaA {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) : (weights v n m X Y).IsWeightDatum := sorry

/-- A corollary that joins the two halves: at a solution over a valued field whose mass weights lie in
W_n(τ), τ ≥ 2n², the valuation of every (X_t − X_l)(Y_t − Y_l) is bounded above in terms of the mass
weights alone. This is the hypothesis of Proposition D2 in Theorem D5′. -/
theorem solution_bound {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) (τ : ℝ) (hτ : 2 * (n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber n τ fun t => (v (m t)).untopD 0) (t l : ℕ) (htl : t < l) (hl : l < n) :
    v ((X t - X l) * (Y t - Y l))
      ≤ ((2 * (2 * (n : ℝ) - 1) * (∑ j ∈ range n, |(v (m j)).untopD 0|) / 3
          + 2 * (v (m t)).untopD 0 + 2 * (v (m l)).untopD 0 : ℝ) : WithTop ℝ) := sorry

end
