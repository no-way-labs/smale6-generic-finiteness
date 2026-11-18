import DirectRoute.Defs

/-!
The definitions of `ChallengeA.lean`, copied without change for the solution.
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

end
