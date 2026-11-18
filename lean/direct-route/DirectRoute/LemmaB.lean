import DirectRoute.Defs

/-!
Lemma B (T1), from the pilot.
-/

open Finset

/-- In the chamber every weight is above `u 0`. -/
theorem chamber_pos {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) :
    ∀ j, 1 ≤ j → j < n → 0 < u j - u 0 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have := hu.1
      simp only [zero_add]
      linarith
    · have h1 := ih hkpos (by omega)
      have h2 := hu.2 (k + 1) (by omega) hk
      simp only [Nat.add_sub_cancel] at h2
      have := mul_nonneg hτ0 h1.le
      linarith

/-- In the chamber the weights increase from index 1 on. -/
theorem chamber_mono {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) :
    ∀ i j, 1 ≤ i → i ≤ j → j < n → u i ≤ u j := by
  intro i j hi hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hik ih =>
    intro hk
    have h1 := ih (by omega)
    have hpos := chamber_pos hu hτ0 k (by omega) (by omega)
    have h2 := hu.2 (k + 1) (by omega) hk
    simp only [Nat.add_sub_cancel] at h2
    have := mul_nonneg hτ0 hpos.le
    linarith

/-- Each gap is more than `τ` times the range below it. -/
theorem chamber_step {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (j : ℕ) (h2 : 2 ≤ j)
    (hj : j < n) : (1 + τ) * (u (j - 1) - u 0) < u j - u 0 := by
  have h := hu.2 j h2 hj
  have e : (1 + τ) * (u (j - 1) - u 0) = (u (j - 1) - u 0) + τ * (u (j - 1) - u 0) := by ring
  rw [e]
  linarith

/-- A sum with the weights is a sum with the differences `u j - u 0` when the coefficients add to 0,
and the term of index 0 drops out. -/
theorem sum_shift (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ) (hm : 0 < m)
    (hsum : ∑ j ∈ range (m + 1), q j = 0) :
    ∑ j ∈ range (m + 1), (q j : ℝ) * u j
      = (q m : ℝ) * (u m - u 0) + ∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0) := by
  have h1 : ∑ j ∈ range (m + 1), (q j : ℝ) * (u j - u 0)
      = ∑ j ∈ range (m + 1), (q j : ℝ) * u j - (∑ j ∈ range (m + 1), (q j : ℝ)) * u 0 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ j ∈ range (m + 1), (q j : ℝ)) = 0 := by exact_mod_cast hsum
  have h3 : ∑ j ∈ range m, (q j : ℝ) * (u j - u 0) = ∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
    simp
  rw [h2, zero_mul, sub_zero, Finset.sum_range_succ, h3] at h1
  linarith

/-- The terms of index 1 to `m - 1` are at most the sum of the `|q j|` times `u (m - 1) - u 0`. -/
theorem sum_bound {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (q : ℕ → ℤ) (m : ℕ)
    (hm : m < n) :
    |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)| ≤ (∑ j ∈ Ico 1 m, |(q j : ℝ)|) * (u (m - 1) - u 0) := by
  calc |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)|
      ≤ ∑ j ∈ Ico 1 m, |(q j : ℝ) * (u j - u 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ico 1 m, |(q j : ℝ)| * (u (m - 1) - u 0) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hpos := chamber_pos hu hτ0 j hj.1 (by omega)
        have hmono := chamber_mono hu hτ0 j (m - 1) hj.1 (by omega) (by omega)
        rw [abs_mul, abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = (∑ j ∈ Ico 1 m, |(q j : ℝ)|) * (u (m - 1) - u 0) := by rw [Finset.sum_mul]

/-- Lemma B (T1). -/
theorem lemmaB_proof (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ)
    (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (hm : m < n) (hqm : q m ≠ 0)
    (hsum : ∑ j ∈ range (m + 1), q j = 0)
    (hτ : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ) :
    ∑ j ∈ range (m + 1), (q j : ℝ) * u j ≠ 0 := by
  intro h0
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp at hsum
    exact hqm hsum
  rw [sum_shift u q m hmpos hsum] at h0
  have hRm : 0 < u m - u 0 := chamber_pos hu hτ0 m hmpos hm
  have hqm' : (0 : ℝ) < |(q m : ℝ)| := abs_pos.mpr (by exact_mod_cast hqm)
  have hbound := sum_bound hu hτ0 q m hm
  have habs : |(q m : ℝ)| * (u m - u 0) = |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)| := by
    have e : (q m : ℝ) * (u m - u 0) = -∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0) := by linarith
    calc |(q m : ℝ)| * (u m - u 0) = |(q m : ℝ) * (u m - u 0)| := by rw [abs_mul, abs_of_pos hRm]
      _ = |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)| := by rw [e, abs_neg]
  rw [← habs] at hbound
  have hS : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) ≤ (1 + τ) * |(q m : ℝ)| := by
    have h : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| ≤ 1 + τ := by linarith
    exact (div_le_iff₀ hqm').mp h
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hm1' : m = 1 := by omega
    subst hm1'
    simp at hbound
    have := mul_pos hqm' hRm
    linarith
  · have hstep := chamber_step hu m hm2 hm
    have hR' : 0 < u (m - 1) - u 0 := chamber_pos hu hτ0 (m - 1) (by omega) (by omega)
    have h1 : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) * (u (m - 1) - u 0)
        ≤ (1 + τ) * |(q m : ℝ)| * (u (m - 1) - u 0) := mul_le_mul_of_nonneg_right hS hR'.le
    have h2 : |(q m : ℝ)| * ((1 + τ) * (u (m - 1) - u 0)) < |(q m : ℝ)| * (u m - u 0) :=
      mul_lt_mul_of_pos_left hstep hqm'
    have e : (1 + τ) * |(q m : ℝ)| * (u (m - 1) - u 0)
        = |(q m : ℝ)| * ((1 + τ) * (u (m - 1) - u 0)) := by ring
    linarith
