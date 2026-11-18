import DirectRoute.Cycle
import DirectRoute.Examples
import DirectRoute.DefsB

/-!
The statements of `ChallengeB.lean`: Lemma 4.1 with the sign, Lemma 5.2 and Theorem 6.2 (b), (c), (d) of
the paper for closed alternating sequences.

Written by `scripts/allN/lean_gen_alt.py`. The sections `alt` and `alt2` are the sections `cycle` and
`cycle2` of `Relation.lean` with the hypothesis `IsAltSeq` in place of `IsCycle`.
-/

open Finset

namespace D4

section alt

variable {D : Datum} {P : ℝ} {r : ℕ} {f g : ℕ → ℕ × ℕ}

theorem adj_whA (_hD : D.IsWeightDatum)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) {i : ℕ} (hi : i < r) :
    wh D (f i) = wh D (g i) := by
  have ef := (hc.mem_f i hi).1
  have eg := (hc.mem_g i hi).1
  have h : D.dw (f i).1 (f i).2 = D.dw (g i).1 (g i).2 := hc.adj_w i hi
  rw [dw_eq D ef, dw_eq D eg] at h
  exact_mod_cast h

theorem adj_zhA (_hD : D.IsWeightDatum)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) {i : ℕ} (hi : i < r) :
    zh D (g i) = zh D (f ((i + 1) % r)) := by
  have hi' : (i + 1) % r < r := Nat.mod_lt _ (by omega)
  have ef := (hc.mem_f _ hi').1
  have eg := (hc.mem_g i hi).1
  have h : D.dz (g i).1 (g i).2 = D.dz (f ((i + 1) % r)).1 (f ((i + 1) % r)).2 := hc.adj_z i hi
  rw [dz_eq D eg, dz_eq D ef] at h
  exact_mod_cast h

/-- Step 2: the relation N Ψ* + q·u = 0. -/
theorem relationA (hD : D.IsWeightDatum)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) :
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 := by
  have hr : 0 < r := hc.pos
  have h1 : (cycN D.n r f g : ℝ) * P
      = ∑ i ∈ range r, ((3 * (if (g i).2 < D.n then (1 : ℝ) else 0) - 1) * P
          - (3 * (if (f i).2 < D.n then (1 : ℝ) else 0) - 1) * P) := by
    unfold cycN
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k
      = ∑ i ∈ range r, (∑ k ∈ range D.n, (inc D.n (g i) k : ℝ) * D.u k
          - ∑ k ∈ range D.n, (inc D.n (f i) k : ℝ) * D.u k) := by
    unfold cycQ
    push_cast
    simp only [Finset.sum_mul, sub_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  have h3 : ∑ i ∈ range r, ((zh D (g i) + wh D (g i)) - (zh D (f i) + wh D (f i))) = 0 := by
    have e : ∀ i ∈ range r, (zh D (g i) + wh D (g i)) - (zh D (f i) + wh D (f i))
        = zh D (f ((i + 1) % r)) - zh D (f i) := by
      intro i hi
      rw [mem_range] at hi
      rw [adj_zhA hD hc hi, adj_whA hD hc hi]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, sum_shift_mod r hr (fun i => zh D (f i))]
    simp
  have h4 : ∑ i ∈ range r, ((zh D (g i) + wh D (g i)) - (zh D (f i) + wh D (f i)))
      = ∑ i ∈ range r, (((3 * (if (g i).2 < D.n then (1 : ℝ) else 0) - 1) * P
            - (3 * (if (f i).2 < D.n then (1 : ℝ) else 0) - 1) * P)
          + (∑ k ∈ range D.n, (inc D.n (g i) k : ℝ) * D.u k
            - ∑ k ∈ range D.n, (inc D.n (f i) k : ℝ) * D.u k)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [val_eq D (hc.mem_g i hi), val_eq D (hc.mem_f i hi)]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib, ← h4, h3]

/-- Step 3: a simple cycle of B has an O-edge. -/
theorem has_OA {τ : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber D.n τ D.u)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) :
    ∃ i, i < r ∧ ((f i).2 = D.n ∨ (g i).2 = D.n) := by
  by_contra hcon
  push_neg at hcon
  have hr : 0 < r := hc.pos
  have hmod : ∀ i, i % r < r := fun i => Nat.mod_lt _ hr
  have ltF : ∀ i, (f (i % r)).1 < (f (i % r)).2 ∧ (f (i % r)).2 < D.n := by
    intro i
    have h := edge_le D (hc.mem_f _ (hmod i)).1
    have := (hcon _ (hmod i)).1
    omega
  have ltG : ∀ i, (g (i % r)).1 < (g (i % r)).2 ∧ (g (i % r)).2 < D.n := by
    intro i
    have h := edge_le D (hc.mem_g _ (hmod i)).1
    have := (hcon _ (hmod i)).2
    omega
  have psiF : ∀ i, psiPair D.u D.z D.w (f (i % r)).1 (f (i % r)).2 = P := by
    intro i
    have h := (hc.mem_f _ (hmod i)).2
    simp only [Datum.psiE, (hcon _ (hmod i)).1, if_false] at h
    exact h
  have psiG : ∀ i, psiPair D.u D.z D.w (g (i % r)).1 (g (i % r)).2 = P := by
    intro i
    have h := (hc.mem_g _ (hmod i)).2
    simp only [Datum.psiE, (hcon _ (hmod i)).2, if_false] at h
    exact h
  have hz : IsUltra D.n fun x y => (D.z x y : WithTop ℝ) := by
    refine ⟨fun x y hx hy => ?_, fun x y t hx hy ht hxy hyt hxt => ?_⟩
    · show (D.z x y : WithTop ℝ) = D.z y x
      rw [← dz_body D hx hy, ← dz_body D hy hx]
      exact hD.ultra_z.1 x y (by omega) (by omega)
    · show min (D.z x y : WithTop ℝ) (D.z y t) ≤ D.z x t
      rw [← dz_body D hx hy, ← dz_body D hy ht, ← dz_body D hx ht]
      exact hD.ultra_z.2 x y t (by omega) (by omega) (by omega) hxy hyt hxt
  have hw : IsUltra D.n fun x y => (D.w x y : WithTop ℝ) := by
    refine ⟨fun x y hx hy => ?_, fun x y t hx hy ht hxy hyt hxt => ?_⟩
    · show (D.w x y : WithTop ℝ) = D.w y x
      rw [← dw_body D hx hy, ← dw_body D hy hx]
      exact hD.ultra_w.1 x y (by omega) (by omega)
    · show min (D.w x y : WithTop ℝ) (D.w y t) ≤ D.w x t
      rw [← dw_body D hx hy, ← dw_body D hy ht, ← dw_body D hx ht]
      exact hD.ultra_w.2 x y t (by omega) (by omega) (by omega) hxy hyt hxt
  have S : LC.Setup D.n D.u D.z D.w r (fun i => f (i % r)) (fun i => g (i % r)) P := by
    refine ⟨hr, ?_, ltF, ltG, psiF, psiG, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro a b hab hb
      have h := hP.1 (a, b) ⟨hab, Or.inl hb⟩
      simp only [Datum.psiE, Nat.ne_of_lt hb, if_false] at h
      exact h
    · intro i
      have h := adj_whA hD hc (hmod i)
      simp only [wh, (hcon _ (hmod i)).1, (hcon _ (hmod i)).2, if_false] at h
      exact h
    · intro i
      have h := adj_zhA hD hc (hmod i)
      have e : (i % r + 1) % r = (i + 1) % r := Nat.mod_add_mod i r 1
      rw [e] at h
      simp only [zh, (hcon _ (hmod i)).2, (hcon _ (hmod (i + 1))).1, if_false] at h
      exact h
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_f i j hi hj h
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_g i j hi hj h
    · intro i j hi hj
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact hc.ne_fg i j hi hj
  have hτ' : (D.n : ℝ) ^ 2 ≤ τ := by nlinarith [sq_nonneg (D.n : ℝ)]
  exact S.contra hu hτ' hz hw

end alt

section alt2

variable {D : Datum} {P : ℝ} {r : ℕ} {f g : ℕ → ℕ × ℕ}

theorem cycQ_decompA (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g)
    (k : ℕ) :
    cycQ D.n r f g k
      = 2 * (∑ i ∈ range r, (if (g i).2 < D.n ∧ ((g i).1 = k ∨ (g i).2 = k) then (1 : ℤ) else 0)
          - ∑ i ∈ range r, (if (f i).2 < D.n ∧ ((f i).1 = k ∨ (f i).2 = k) then (1 : ℤ) else 0))
        - (∑ i ∈ range r, (if (g i).2 = D.n ∧ (g i).1 = k then (1 : ℤ) else 0)
          - ∑ i ∈ range r, (if (f i).2 = D.n ∧ (f i).1 = k then (1 : ℤ) else 0)) := by
  unfold cycQ
  have e : ∀ i ∈ range r, inc D.n (g i) k - inc D.n (f i) k
      = 2 * ((if (g i).2 < D.n ∧ ((g i).1 = k ∨ (g i).2 = k) then (1 : ℤ) else 0)
          - (if (f i).2 < D.n ∧ ((f i).1 = k ∨ (f i).2 = k) then (1 : ℤ) else 0))
        - ((if (g i).2 = D.n ∧ (g i).1 = k then (1 : ℤ) else 0)
          - (if (f i).2 = D.n ∧ (f i).1 = k then (1 : ℤ) else 0)) := by
    intro i hi
    rw [mem_range] at hi
    rw [inc_decomp D.n (g i) k (edge_le D (hc.mem_g i hi).1).2,
      inc_decomp D.n (f i) k (edge_le D (hc.mem_f i hi).1).2]
    ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- |q_k| ≤ 2n − 1. -/
theorem cycQ_absA (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g)
    {k : ℕ} (hk : k < D.n) : |(cycQ D.n r f g k : ℝ)| ≤ 2 * (D.n : ℝ) - 1 := by
  have lf : ∀ i, i < r → (f i).1 < (f i).2 := fun i hi => (edge_le D (hc.mem_f i hi).1).1
  have lg : ∀ i, i < r → (g i).1 < (g i).2 := fun i hi => (edge_le D (hc.mem_g i hi).1).1
  have h1 := pb_le (n := D.n) lf hc.inj_f hk
  have h2 := pb_le (n := D.n) lg hc.inj_g hk
  have h3 := pb_nonneg (n := D.n) (r := r) (h := f) k
  have h4 := pb_nonneg (n := D.n) (r := r) (h := g) k
  have h5 := ob_le (n := D.n) hc.inj_f k
  have h6 := ob_le (n := D.n) hc.inj_g k
  have h7 := ob_nonneg (n := D.n) (r := r) (h := f) k
  have h8 := ob_nonneg (n := D.n) (r := r) (h := g) k
  have h9 : |cycQ D.n r f g k| ≤ 2 * (D.n : ℤ) - 1 := by
    rw [cycQ_decompA hc k, abs_le]
    constructor <;> linarith
  exact_mod_cast h9

/-- The parity step: the coefficient of the body of an O-edge of the cycle is odd. -/
theorem cycQ_ne_zeroA (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g)
    {i0 : ℕ} (hi0 : i0 < r) (hO : (f i0).2 = D.n ∨ (g i0).2 = D.n) :
    ∃ t, t < D.n ∧ cycQ D.n r f g t ≠ 0 := by
  rcases hO with hO | hO
  · refine ⟨(f i0).1, ?_, ?_⟩
    · have := (edge_le D (hc.mem_f i0 hi0).1).1
      omega
    · have hf1 : ∑ i ∈ range r, (if (f i).2 = D.n ∧ (f i).1 = (f i0).1 then (1 : ℤ) else 0) = 1 := by
        apply le_antisymm (ob_le hc.inj_f _)
        have := Finset.single_le_sum
          (f := fun i => if (f i).2 = D.n ∧ (f i).1 = (f i0).1 then (1 : ℤ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (mem_range.mpr hi0)
        simpa [hO] using this
      have hg0 : ∑ i ∈ range r, (if (g i).2 = D.n ∧ (g i).1 = (f i0).1 then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [mem_range] at hj
        have hne : ¬((g j).2 = D.n ∧ (g j).1 = (f i0).1) := by
          rintro ⟨h1, h2⟩
          exact hc.ne_fg i0 j hi0 hj (Prod.ext h2.symm (hO.trans h1.symm))
        simp [hne]
      rw [cycQ_decompA hc, hf1, hg0]
      omega
  · refine ⟨(g i0).1, ?_, ?_⟩
    · have := (edge_le D (hc.mem_g i0 hi0).1).1
      omega
    · have hg1 : ∑ i ∈ range r, (if (g i).2 = D.n ∧ (g i).1 = (g i0).1 then (1 : ℤ) else 0) = 1 := by
        apply le_antisymm (ob_le hc.inj_g _)
        have := Finset.single_le_sum
          (f := fun i => if (g i).2 = D.n ∧ (g i).1 = (g i0).1 then (1 : ℤ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (mem_range.mpr hi0)
        simpa [hO] using this
      have hf0 : ∑ i ∈ range r, (if (f i).2 = D.n ∧ (f i).1 = (g i0).1 then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [mem_range] at hj
        have hne : ¬((f j).2 = D.n ∧ (f j).1 = (g i0).1) := by
          rintro ⟨h1, h2⟩
          exact hc.ne_fg j i0 hj hi0 (Prod.ext h2 (h1.trans hO.symm))
        simp [hne]
      rw [cycQ_decompA hc, hg1, hf0]
      omega

/-- Step 4: N ≠ 0. -/
theorem N_ne_zeroA {τ : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber D.n τ D.u)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) :
    cycN D.n r f g ≠ 0 := by
  intro hN
  have hrel := relationA hD hc
  rw [hN] at hrel
  simp only [Int.cast_zero, zero_mul, zero_add] at hrel
  have hqsum : ∑ k ∈ range D.n, cycQ D.n r f g k = 0 := by
    unfold cycQ
    rw [Finset.sum_comm]
    have e : ∀ i ∈ range r, ∑ k ∈ range D.n, (inc D.n (g i) k - inc D.n (f i) k)
        = 5 * ((if (g i).2 < D.n then (1 : ℤ) else 0) - (if (f i).2 < D.n then (1 : ℤ) else 0)) := by
      intro i hi
      rw [mem_range] at hi
      rw [Finset.sum_sub_distrib, sum_inc D (hc.mem_g i hi).1, sum_inc D (hc.mem_f i hi).1]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    unfold cycN at hN
    have : ∑ i ∈ range r, ((if (g i).2 < D.n then (1 : ℤ) else 0) - (if (f i).2 < D.n then (1 : ℤ) else 0))
        = 0 := by linarith
    rw [this]
    norm_num
  obtain ⟨i0, hi0, hO⟩ := has_OA hD hP hτ hu hc
  obtain ⟨t, ht, hqt⟩ := cycQ_ne_zeroA hc hi0 hO
  have hτ0 : 0 ≤ τ := by nlinarith [sq_nonneg (D.n : ℝ)]
  have hBτ : (D.n : ℝ) * (2 * (D.n : ℝ) - 1) ≤ τ + 1 := by
    have : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
    nlinarith
  exact hqt (lemmaB_apply hu hτ0 (cycQ D.n r f g) (2 * (D.n : ℝ) - 1) (fun k hk => cycQ_absA hc hk)
    hBτ hqsum hrel t ht)

end alt2

end D4

/-- Lemma 4.1 with the sign. -/
theorem lemmaB_sign_proof (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ)
    (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (hm : m < n) (hqm : q m ≠ 0)
    (hsum : ∑ j ∈ range (m + 1), q j = 0)
    (hτ : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ) :
    0 < (q m : ℝ) * ∑ j ∈ range (m + 1), (q j : ℝ) * u j := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp at hsum
    exact absurd hsum hqm
  rw [sum_shift u q m hmpos hsum]
  have hRm : 0 < u m - u 0 := chamber_pos hu hτ0 m hmpos hm
  have hqm' : (0 : ℝ) < |(q m : ℝ)| := abs_pos.mpr (by exact_mod_cast hqm)
  have hbound := sum_bound hu hτ0 q m hm
  have hS : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) ≤ (1 + τ) * |(q m : ℝ)| := by
    have h : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| ≤ 1 + τ := by linarith
    exact (div_le_iff₀ hqm').mp h
  have hlt : |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)| < |(q m : ℝ)| * (u m - u 0) := by
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have hI : Ico 1 m = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hI, Finset.sum_empty, abs_zero]
      exact mul_pos hqm' hRm
    · have hstep := chamber_step hu m hm2 hm
      have hR' : 0 < u (m - 1) - u 0 := chamber_pos hu hτ0 (m - 1) (by omega) (by omega)
      have h1 : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) * (u (m - 1) - u 0)
          ≤ (1 + τ) * |(q m : ℝ)| * (u (m - 1) - u 0) := mul_le_mul_of_nonneg_right hS hR'.le
      have h2 : |(q m : ℝ)| * ((1 + τ) * (u (m - 1) - u 0)) < |(q m : ℝ)| * (u m - u 0) :=
        mul_lt_mul_of_pos_left hstep hqm'
      have e : (1 + τ) * |(q m : ℝ)| * (u (m - 1) - u 0)
          = |(q m : ℝ)| * ((1 + τ) * (u (m - 1) - u 0)) := by ring
      linarith
  have h3 : -(|(q m : ℝ)| * |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)|)
      ≤ (q m : ℝ) * ∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0) := by
    have h := neg_abs_le ((q m : ℝ) * ∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0))
    rw [abs_mul] at h
    exact h
  have hsq : |(q m : ℝ)| * |(q m : ℝ)| = (q m : ℝ) * (q m : ℝ) := abs_mul_abs_self _
  have h4 : (q m : ℝ) * ((q m : ℝ) * (u m - u 0)) = |(q m : ℝ)| * (|(q m : ℝ)| * (u m - u 0)) := by
    calc (q m : ℝ) * ((q m : ℝ) * (u m - u 0)) = ((q m : ℝ) * (q m : ℝ)) * (u m - u 0) := by ring
      _ = (|(q m : ℝ)| * |(q m : ℝ)|) * (u m - u 0) := by rw [hsq]
      _ = |(q m : ℝ)| * (|(q m : ℝ)| * (u m - u 0)) := by ring
  have h5 : |(q m : ℝ)| * |∑ j ∈ Ico 1 m, (q j : ℝ) * (u j - u 0)|
      < |(q m : ℝ)| * (|(q m : ℝ)| * (u m - u 0)) := mul_lt_mul_of_pos_left hlt hqm'
  rw [mul_add, h4]
  linarith

/-- Lemma 5.2. -/
theorem lemmaC_alt_proof (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hτ : (n : ℝ) ^ 2 ≤ τ) (hu : Chamber n τ u)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    ¬ ∃ r f g, IsAltSeq (topPairs n u z w) (fun e => z e.1 e.2) (fun e => w e.1 e.2) r f g := by
  rintro ⟨r, f, g, hc⟩
  have hr : 0 < r := hc.pos
  have hmod : ∀ i, i % r < r := fun i => Nat.mod_lt _ hr
  have memF : ∀ i, f (i % r) ∈ topPairs n u z w := fun i => hc.mem_f _ (hmod i)
  have memG : ∀ i, g (i % r) ∈ topPairs n u z w := fun i => hc.mem_g _ (hmod i)
  have h0 := hc.mem_f 0 hr
  have hP : ∀ e, e ∈ topPairs n u z w →
      psiPair u z w e.1 e.2 = psiPair u z w (f 0).1 (f 0).2 := fun e he =>
    le_antisymm (h0.2.2 e.1 e.2 he.1 he.2.1) (he.2.2 _ _ h0.1 h0.2.1)
  have S : LC.Setup n u z w r (fun i => f (i % r)) (fun i => g (i % r))
      (psiPair u z w (f 0).1 (f 0).2) := by
    refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · exact fun i => ⟨(memF i).1, (memF i).2.1⟩
    · exact fun i => ⟨(memG i).1, (memG i).2.1⟩
    · exact fun i => hP _ (memF i)
    · exact fun i => hP _ (memG i)
    · exact fun a b hab hb => h0.2.2 a b hab hb
    · intro i
      exact hc.adj_w _ (hmod i)
    · intro i
      have e : (i % r + 1) % r = (i + 1) % r := Nat.mod_add_mod i r 1
      have hadj : z (g (i % r)).1 (g (i % r)).2
          = z (f ((i % r + 1) % r)).1 (f ((i % r + 1) % r)).2 := hc.adj_z _ (hmod i)
      rw [e] at hadj
      exact hadj
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_f i j hi hj h
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_g i j hi hj h
    · intro i j hi hj
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact hc.ne_fg i j hi hj
  exact S.contra hu hτ hz hw

/-- A simple cycle of the pairs of E° is a closed alternating sequence. -/
theorem cycle_alt_bodies_proof (n : ℕ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ))
    (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (topPairs n u z w) (node n fun x y => (z x y : WithTop ℝ))
      (node n fun x y => (w x y : WithTop ℝ)) r f g) :
    IsAltSeq (topPairs n u z w) (fun e => z e.1 e.2) (fun e => w e.1 e.2) r f g := by
  have hr : 0 < r := hc.pos
  refine ⟨hc.pos, hc.mem_f, hc.mem_g, ?_, ?_, hc.inj_f, hc.inj_g, hc.ne_fg⟩
  · intro i hi
    have mf := hc.mem_f i hi
    have mg := hc.mem_g i hi
    exact LC.node_height_eq hw (lt_trans mf.1 mf.2.1) mf.2.1 (lt_trans mg.1 mg.2.1) mg.2.1
      (Nat.ne_of_lt mf.1) (Nat.ne_of_lt mg.1) (hc.adj_w i hi)
  · intro i hi
    have hi' : (i + 1) % r < r := Nat.mod_lt _ hr
    have mf := hc.mem_f _ hi'
    have mg := hc.mem_g i hi
    exact LC.node_height_eq hz (lt_trans mg.1 mg.2.1) mg.2.1 (lt_trans mf.1 mf.2.1) mf.2.1
      (Nat.ne_of_lt mg.1) (Nat.ne_of_lt mf.1) (hc.adj_z i hi)

/-- Theorem 6.2 (b), (c). -/
theorem alt_relation_proof (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) :
    (∃ i, i < r ∧ ((f i).2 = D.n ∨ (g i).2 = D.n)) ∧
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 ∧
      cycN D.n r f g ≠ 0 :=
  ⟨D4.has_OA hD hP hτ hu hc, D4.relationA hD hc, D4.N_ne_zeroA hD hP hτ hu hc⟩

/-- A simple cycle of the graph of E* is a closed alternating sequence. -/
theorem cycle_alt_proof (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g := by
  have hr : 0 < r := hc.pos
  refine ⟨hc.pos, hc.mem_f, hc.mem_g, ?_, ?_, hc.inj_f, hc.inj_g, hc.ne_fg⟩
  · intro i hi
    have lf := D4.edge_le D (hc.mem_f i hi).1
    have lg := D4.edge_le D (hc.mem_g i hi).1
    exact D4.node_height_eq hD.ultra_w (a := (f i).1) (b := (f i).2) (a' := (g i).1) (b' := (g i).2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (hc.adj_w i hi)
  · intro i hi
    have hi' : (i + 1) % r < r := Nat.mod_lt _ hr
    have lf := D4.edge_le D (hc.mem_f _ hi').1
    have lg := D4.edge_le D (hc.mem_g i hi).1
    exact D4.node_height_eq hD.ultra_z (a := (g i).1) (b := (g i).2) (a' := (f ((i + 1) % r)).1)
      (b' := (f ((i + 1) % r)).2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hc.adj_z i hi)

/-- Theorem 6.2 (d), the bound. -/
theorem psi_star_bound_proof (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) :
    P ≤ (2 * (D.n : ℝ) - 1) * (∑ j ∈ range D.n, |D.u j|) / 3 := by
  obtain ⟨r, f, g, hc⟩ := exists_cycle_proof D P hD hP
  obtain ⟨hrel, hN⟩ := cycle_relation_proof D P τ hD hP hτ hu r f g hc
  have hN3 : (3 : ℝ) ≤ |(cycN D.n r f g : ℝ)| := by
    have h3 : (3 : ℤ) ≤ |cycN D.n r f g| := by
      obtain ⟨X, hX⟩ : ∃ X : ℤ, cycN D.n r f g = 3 * X := ⟨_, rfl⟩
      rw [hX] at hN ⊢
      rw [le_abs]
      have hX0 : X ≠ 0 := fun h0 => hN (by rw [h0]; norm_num)
      omega
    exact_mod_cast h3
  have hsum : |∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k|
      ≤ (2 * (D.n : ℝ) - 1) * ∑ k ∈ range D.n, |D.u k| := by
    calc |∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k|
        ≤ ∑ k ∈ range D.n, |(cycQ D.n r f g k : ℝ) * D.u k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range D.n, (2 * (D.n : ℝ) - 1) * |D.u k| := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (D4.cycQ_abs hc (mem_range.mp hk)) (abs_nonneg _)
      _ = (2 * (D.n : ℝ) - 1) * ∑ k ∈ range D.n, |D.u k| := by rw [Finset.mul_sum]
  have e1 : (cycN D.n r f g : ℝ) * P = -∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k := by
    linarith
  have e2 : |(cycN D.n r f g : ℝ)| * |P| = |∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k| := by
    rw [← abs_mul, e1, abs_neg]
  have e3 := mul_le_mul_of_nonneg_right hN3 (abs_nonneg P)
  have e4 := le_abs_self P
  linarith

/-- The example n = 2. -/
theorem ex2_alt_proof :
    IsAltSeq (ex2.Estar (-2)) (fun e => ex2.dz e.1 e.2) (fun e => ex2.dw e.1 e.2) 1
      (fun _ => (0, 1)) (fun _ => (1, 2)) :=
  cycle_alt_proof ex2 (-2) Ex2.datum 1 _ _ Ex2.cycle

/-- The example at the weights (0, 0, 1, 1). -/
theorem ex4_alt_proof :
    IsAltSeq (topPairs 4 ex4u ex4z ex4w) (fun e => ex4z e.1 e.2) (fun e => ex4w e.1 e.2) 2
      (fun i => if i = 0 then (0, 1) else (2, 3)) (fun i => if i = 0 then (1, 2) else (0, 3)) :=
  cycle_alt_bodies_proof 4 ex4u ex4z ex4w Ex4.ultra_z Ex4.ultra_w 2 _ _ Ex4.cycle
