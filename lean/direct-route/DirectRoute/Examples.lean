import DirectRoute.Defs

/-!
Proofs of the tests E1 to E4 of the definitions.
-/

open Finset

/-- E1. -/
theorem chamber_nonempty_proof (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : ∃ u, Chamber n τ u := by
  refine ⟨fun j => (τ + 2) ^ j, ?_, ?_⟩
  · simp only [pow_zero, pow_one]
    linarith
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have ha : 0 < (τ + 2) ^ k := by positivity
    simp only [Nat.add_sub_cancel, pow_zero, pow_succ]
    nlinarith

/-- The numeral 2 of `WithTop ℝ` is the real number 2. -/
theorem untopD_two : WithTop.untopD (0 : ℝ) (2 : WithTop ℝ) = 2 := by
  have h : (2 : WithTop ℝ) = ((2 : ℝ) : WithTop ℝ) := by norm_cast
  rw [h, WithTop.untopD_coe]

theorem two_not_le_zero : ¬((2 : WithTop ℝ) ≤ 0) := by
  intro h
  have h' : ((2 : ℝ) : WithTop ℝ) ≤ ((0 : ℝ) : WithTop ℝ) := by exact_mod_cast h
  exact absurd (WithTop.coe_le_coe.mp h') (by norm_num)

namespace Ex2

theorem ultra_z : IsUltra 3 ex2.dz := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dz, ex2]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dz, ex2]

theorem ultra_w : IsUltra 3 ex2.dw := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dw, ex2]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dw, ex2]

/-- A cut condition holds when all its terms have one value and there are two of them. -/
theorem _root_.Datum.cutZ_of_const (D : Datum) (S : Finset ℕ) (c : ℝ)
    (hval : ∀ e, e ∈ D.termsZ S → D.phiZ e.1 e.2 = c) (e₁ e₂ : ℕ × ℕ)
    (h₁ : e₁ ∈ D.termsZ S) (h₂ : e₂ ∈ D.termsZ S) (hne : e₁ ≠ e₂) : D.CutZ S :=
  ⟨e₁, e₂, h₁, h₂, hne, by rw [hval _ h₁, hval _ h₂], fun e he => by rw [hval _ he, hval _ h₁]⟩

theorem _root_.Datum.cutW_of_const (D : Datum) (S : Finset ℕ) (c : ℝ)
    (hval : ∀ e, e ∈ D.termsW S → D.phiW e.1 e.2 = c) (e₁ e₂ : ℕ × ℕ)
    (h₁ : e₁ ∈ D.termsW S) (h₂ : e₂ ∈ D.termsW S) (hne : e₁ ≠ e₂) : D.CutW S :=
  ⟨e₁, e₂, h₁, h₂, hne, by rw [hval _ h₁, hval _ h₂], fun e he => by rw [hval _ he, hval _ h₁]⟩

theorem phiZ_val : ∀ t y, t < 2 → y ≤ 2 → t ≠ y → ex2.phiZ t y = -2 := by
  intro t y ht hy hty
  interval_cases t <;> interval_cases y <;> simp_all [Datum.phiZ, psiPair, ex2, untopD_two]

theorem phiW_val : ∀ t y, t < 2 → y ≤ 2 → t ≠ y → ex2.phiW t y = -2 := by
  intro t y ht hy hty
  interval_cases t <;> interval_cases y <;> simp_all [Datum.phiW, psiPair, ex2, untopD_two]

theorem cut_z (S : Finset ℕ) (hS : S ⊆ range 2) (hne : S.Nonempty) : ex2.CutZ S := by
  have hlt : ∀ t, t ∈ S → t < 2 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex2.termsZ S → ex2.phiZ e.1 e.2 = -2 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha2 := hlt a ha
    rcases hb with ⟨hb, hbS⟩ | ⟨hb, _⟩
    · exact phiZ_val a b ha2 (by simp [ex2] at hb; omega) (by rintro rfl; exact hbS ha)
    · exact phiZ_val a b ha2 (by simp [ex2] at hb; omega) (by simp [ex2] at hb; omega)
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S
  · exact ex2.cutZ_of_const S _ hval (0, 2) (1, 2) ⟨h0, Or.inr ⟨rfl, by simp [ex2]⟩⟩
      ⟨h1, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · exact ex2.cutZ_of_const S _ hval (0, 1) (0, 2) ⟨h0, Or.inl ⟨by simp [ex2], h1⟩⟩
      ⟨h0, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · exact ex2.cutZ_of_const S _ hval (1, 0) (1, 2) ⟨h1, Or.inl ⟨by simp [ex2], h0⟩⟩
      ⟨h1, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · obtain ⟨t, ht⟩ := hne
    have := hlt t ht
    interval_cases t <;> contradiction

theorem cut_w (S : Finset ℕ) (hS : S ⊆ range 2) (hne : S.Nonempty) : ex2.CutW S := by
  have hlt : ∀ t, t ∈ S → t < 2 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex2.termsW S → ex2.phiW e.1 e.2 = -2 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha2 := hlt a ha
    rcases hb with ⟨hb, hbS⟩ | ⟨hb, _⟩
    · exact phiW_val a b ha2 (by simp [ex2] at hb; omega) (by rintro rfl; exact hbS ha)
    · exact phiW_val a b ha2 (by simp [ex2] at hb; omega) (by simp [ex2] at hb; omega)
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S
  · exact ex2.cutW_of_const S _ hval (0, 2) (1, 2) ⟨h0, Or.inr ⟨rfl, by simp [ex2]⟩⟩
      ⟨h1, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · exact ex2.cutW_of_const S _ hval (0, 1) (0, 2) ⟨h0, Or.inl ⟨by simp [ex2], h1⟩⟩
      ⟨h0, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · exact ex2.cutW_of_const S _ hval (1, 0) (1, 2) ⟨h1, Or.inl ⟨by simp [ex2], h0⟩⟩
      ⟨h1, Or.inr ⟨rfl, by simp [ex2]⟩⟩ (by simp)
  · obtain ⟨t, ht⟩ := hne
    have := hlt t ht
    interval_cases t <;> contradiction

theorem datum : ex2.IsWeightDatum where
  two := le_refl 2
  ultra_z := ultra_z
  ultra_w := ultra_w
  cut_z := cut_z
  cut_w := cut_w

theorem psiE_vals : ex2.psiE (0, 1) = -2 ∧ ex2.psiE (1, 2) = -2 ∧ ex2.psiE (0, 2) = -4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Datum.psiE, Datum.psiO, psiPair, ex2, untopD_two] <;> norm_num

theorem edges : ∀ e, ex2.IsEdge e → e = (0, 1) ∨ e = (0, 2) ∨ e = (1, 2) := by
  rintro ⟨a, b⟩ ⟨hab, h | ⟨hb, _, _⟩⟩
  · simp [ex2] at h hab ⊢
    omega
  · simp [ex2] at hb hab ⊢
    omega

theorem edge01 : ex2.IsEdge (0, 1) := ⟨by simp, Or.inl (by simp [ex2])⟩

theorem edge12 : ex2.IsEdge (1, 2) := ⟨by simp, Or.inr ⟨rfl, by simp [ex2], by simp [ex2]⟩⟩

theorem psiStar : ex2.IsPsiStar (-2) := by
  refine ⟨fun e he => ?_, ⟨(0, 1), edge01, psiE_vals.1⟩⟩
  rcases edges e he with rfl | rfl | rfl
  · rw [psiE_vals.1]
  · rw [psiE_vals.2.2]; norm_num
  · rw [psiE_vals.2.1]

theorem estar_iff (e : ℕ × ℕ) : e ∈ ex2.Estar (-2) ↔ e = (0, 1) ∨ e = (1, 2) := by
  constructor
  · rintro ⟨he, hv⟩
    rcases edges e he with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [psiE_vals.2.2] at hv; norm_num at hv
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨edge01, psiE_vals.1⟩
    · exact ⟨edge12, psiE_vals.2.1⟩

theorem node_z (e : ℕ × ℕ) (he : e = (0, 1) ∨ e = (1, 2)) : node 3 ex2.dz e = range 3 := by
  ext p
  simp only [node, mem_filter, mem_range]
  constructor
  · exact fun h => h.1
  · intro hp
    refine ⟨hp, ?_⟩
    rcases he with rfl | rfl <;> interval_cases p <;> simp [Datum.dz, ex2]

theorem node_w (e : ℕ × ℕ) (he : e = (0, 1) ∨ e = (1, 2)) : node 3 ex2.dw e = range 3 := by
  ext p
  simp only [node, mem_filter, mem_range]
  constructor
  · exact fun h => h.1
  · intro hp
    refine ⟨hp, ?_⟩
    rcases he with rfl | rfl <;> interval_cases p <;> simp [Datum.dw, ex2]

theorem cycle : IsCycle (ex2.Estar (-2)) (node 3 ex2.dz) (node 3 ex2.dw) 1
    (fun _ => (0, 1)) (fun _ => (1, 2)) where
  pos := le_refl 1
  mem_f := fun _ _ => (estar_iff _).mpr (Or.inl rfl)
  mem_g := fun _ _ => (estar_iff _).mpr (Or.inr rfl)
  adj_w := fun _ _ => by rw [node_w _ (Or.inl rfl), node_w _ (Or.inr rfl)]
  adj_z := fun _ _ => by rw [node_z _ (Or.inl rfl), node_z _ (Or.inr rfl)]
  inj_f := fun i j hi hj _ => by omega
  inj_g := fun i j hi hj _ => by omega
  ne_fg := fun _ _ _ _ h => by simp at h
  inj_w := fun i j hi hj _ => by omega
  inj_z := fun i j hi hj _ => by omega

theorem spec :
    ex2.IsWeightDatum ∧ ex2.IsPsiStar (-2) ∧
    (∀ e, e ∈ ex2.Estar (-2) ↔ e = (0, 1) ∨ e = (1, 2)) ∧
    IsCycle (ex2.Estar (-2)) (node 3 ex2.dz) (node 3 ex2.dw) 1 (fun _ => (0, 1)) (fun _ => (1, 2)) ∧
    cycN 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) = -3 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 0 = -2 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 1 = -3 :=
  ⟨datum, psiStar, estar_iff, cycle, by simp [cycN], by simp [cycQ, inc], by simp [cycQ, inc]⟩

end Ex2

namespace Ex3

theorem ultra_z : IsUltra 4 ex3.dz := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dz, ex3]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dz, ex3]

theorem ultra_w : IsUltra 4 ex3.dw := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dw, ex3]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dw, ex3]

theorem phiZ_val (t y : ℕ) : ex3.phiZ t y = 0 := by
  by_cases ht : t = 1 <;> by_cases hy : y = 3 <;> simp [Datum.phiZ, psiPair, ex3, ht, hy]

theorem phiW_val (t y : ℕ) : ex3.phiW t y = 0 := by
  by_cases ht : t = 1 <;> by_cases hy : y = 3 <;> simp [Datum.phiW, psiPair, ex3, ht, hy]

theorem cut_z (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3.CutZ S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex3.termsZ S → ex3.phiZ e.1 e.2 = 0 := fun e _ => phiZ_val _ _
  by_cases h0 : 0 ∈ S
  · have m0 : (0, 3) ∈ ex3.termsZ S := ⟨h0, Or.inr ⟨rfl, by simp [ex3]⟩⟩
    by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · exact ex3.cutZ_of_const S _ hval _ (2, 3) m0 ⟨h2, Or.inr ⟨rfl, by simp [ex3]⟩⟩ (by simp)
      · exact ex3.cutZ_of_const S _ hval _ (0, 2) m0 ⟨h0, Or.inl ⟨by simp [ex3], h2⟩⟩ (by simp)
    · exact ex3.cutZ_of_const S _ hval _ (0, 1) m0 ⟨h0, Or.inl ⟨by simp [ex3], h1⟩⟩ (by simp)
  · by_cases h2 : 2 ∈ S
    · exact ex3.cutZ_of_const S _ hval (2, 3) (2, 0) ⟨h2, Or.inr ⟨rfl, by simp [ex3]⟩⟩
        ⟨h2, Or.inl ⟨by simp [ex3], h0⟩⟩ (by simp)
    · by_cases h1 : 1 ∈ S
      · exact ex3.cutZ_of_const S _ hval (1, 0) (1, 2) ⟨h1, Or.inl ⟨by simp [ex3], h0⟩⟩
          ⟨h1, Or.inl ⟨by simp [ex3], h2⟩⟩ (by simp)
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem cut_w (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3.CutW S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex3.termsW S → ex3.phiW e.1 e.2 = 0 := fun e _ => phiW_val _ _
  by_cases h0 : 0 ∈ S
  · have m0 : (0, 3) ∈ ex3.termsW S := ⟨h0, Or.inr ⟨rfl, by simp [ex3]⟩⟩
    by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · exact ex3.cutW_of_const S _ hval _ (2, 3) m0 ⟨h2, Or.inr ⟨rfl, by simp [ex3]⟩⟩ (by simp)
      · exact ex3.cutW_of_const S _ hval _ (0, 2) m0 ⟨h0, Or.inl ⟨by simp [ex3], h2⟩⟩ (by simp)
    · exact ex3.cutW_of_const S _ hval _ (0, 1) m0 ⟨h0, Or.inl ⟨by simp [ex3], h1⟩⟩ (by simp)
  · by_cases h2 : 2 ∈ S
    · exact ex3.cutW_of_const S _ hval (2, 3) (2, 0) ⟨h2, Or.inr ⟨rfl, by simp [ex3]⟩⟩
        ⟨h2, Or.inl ⟨by simp [ex3], h0⟩⟩ (by simp)
    · by_cases h1 : 1 ∈ S
      · exact ex3.cutW_of_const S _ hval (1, 0) (1, 2) ⟨h1, Or.inl ⟨by simp [ex3], h0⟩⟩
          ⟨h1, Or.inl ⟨by simp [ex3], h2⟩⟩ (by simp)
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem psiE_val (e : ℕ × ℕ) : ex3.psiE e = 0 := by
  by_cases h1 : e.1 = 1 <;> by_cases h2 : e.2 = 3 <;> simp [Datum.psiE, Datum.psiO, psiPair, ex3, h1, h2]

theorem spec :
    ex3.IsWeightDatum ∧ ex3.IsPsiStar 0 ∧ (1, 3) ∉ ex3.Estar 0 ∧ (0, 3) ∈ ex3.Estar 0 := by
  refine ⟨⟨by simp [ex3], ultra_z, ultra_w, cut_z, cut_w⟩, ?_, ?_, ?_⟩
  · exact ⟨fun e _ => by rw [psiE_val], ⟨(0, 1), ⟨by simp, Or.inl (by simp [ex3])⟩, psiE_val _⟩⟩
  · rintro ⟨⟨_, h | ⟨_, hxi, _⟩⟩, _⟩
    · simp [ex3] at h
    · simp [ex3] at hxi
  · exact ⟨⟨by simp, Or.inr ⟨rfl, by simp [ex3], by simp [ex3]⟩⟩, psiE_val _⟩

end Ex3

theorem untopD_one : WithTop.untopD (0 : ℝ) (1 : WithTop ℝ) = 1 := by
  have h : (1 : WithTop ℝ) = ((1 : ℝ) : WithTop ℝ) := by norm_cast
  rw [h, WithTop.untopD_coe]

namespace Ex3c

theorem ultra_z : IsUltra 4 ex3c.dz := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dz, ex3c]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dz, ex3c]

theorem ultra_w : IsUltra 4 ex3c.dw := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dw, ex3c]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dw, ex3c]

/-- An upper bound for the terms of a cut that start at the body `a`. -/
def c (a : ℕ) : ℝ := if a = 2 then -20 else -1

theorem c_le (a : ℕ) : c a ≤ -1 := by
  unfold c
  split_ifs <;> norm_num

theorem phiZ_le : ∀ a b, a < 3 → b ≤ 3 → a ≠ b → ex3c.phiZ a b ≤ c a := by
  intro a b ha hb hab
  interval_cases a <;> interval_cases b <;> simp_all [Datum.phiZ, psiPair, ex3c, c, untopD_one] <;>
    norm_num

theorem vZ : ex3c.phiZ 0 3 = -1 ∧ ex3c.phiZ 1 3 = -1 ∧ ex3c.phiZ 0 1 = -1 ∧ ex3c.phiZ 1 0 = -1 ∧
    ex3c.phiZ 2 0 = -20 ∧ ex3c.phiZ 2 3 = -20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Datum.phiZ, psiPair, ex3c, untopD_one] <;> norm_num

theorem cut_z (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3c.CutZ S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hle : ∀ e, e ∈ ex3c.termsZ S → ex3c.phiZ e.1 e.2 ≤ c e.1 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha3 := hlt a ha
    rcases hb with ⟨hb, hbS⟩ | ⟨hb, _⟩
    · exact phiZ_le a b ha3 (by simp [ex3c] at hb; omega) (by rintro rfl; exact hbS ha)
    · exact phiZ_le a b ha3 (by simp [ex3c] at hb; omega) (by simp [ex3c] at hb; omega)
  obtain ⟨v03, v13, v01, v10, v20, v23⟩ := vZ
  by_cases h0 : 0 ∈ S
  · by_cases h1 : 1 ∈ S
    · refine ⟨(0, 3), (1, 3), ⟨h0, Or.inr ⟨rfl, by simp [ex3c]⟩⟩, ⟨h1, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v03, v13], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v03]
      linarith
    · refine ⟨(0, 1), (0, 3), ⟨h0, Or.inl ⟨by simp [ex3c], h1⟩⟩, ⟨h0, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v01, v03], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v01]
      linarith
  · by_cases h1 : 1 ∈ S
    · refine ⟨(1, 0), (1, 3), ⟨h1, Or.inl ⟨by simp [ex3c], h0⟩⟩, ⟨h1, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v10, v13], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v10]
      linarith
    · by_cases h2 : 2 ∈ S
      · refine ⟨(2, 0), (2, 3), ⟨h2, Or.inl ⟨by simp [ex3c], h0⟩⟩, ⟨h2, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
          by simp, by rw [v20, v23], fun e he => ?_⟩
        have h := hle e he
        have he2 : e.1 = 2 := by
          have h3 := hlt e.1 he.1
          have n0 : e.1 ≠ 0 := fun hh => h0 (hh ▸ he.1)
          have n1 : e.1 ≠ 1 := fun hh => h1 (hh ▸ he.1)
          omega
        have hc : c e.1 = -20 := by rw [he2]; simp [c]
        rw [v20]
        linarith
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem phiW_le : ∀ a b, a < 3 → b ≤ 3 → a ≠ b → ex3c.phiW a b ≤ c a := by
  intro a b ha hb hab
  interval_cases a <;> interval_cases b <;> simp_all [Datum.phiW, psiPair, ex3c, c, untopD_one] <;>
    norm_num

theorem vW : ex3c.phiW 0 3 = -1 ∧ ex3c.phiW 1 3 = -1 ∧ ex3c.phiW 0 1 = -1 ∧ ex3c.phiW 1 0 = -1 ∧
    ex3c.phiW 2 0 = -20 ∧ ex3c.phiW 2 3 = -20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Datum.phiW, psiPair, ex3c, untopD_one] <;> norm_num

theorem cut_w (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3c.CutW S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hle : ∀ e, e ∈ ex3c.termsW S → ex3c.phiW e.1 e.2 ≤ c e.1 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha3 := hlt a ha
    rcases hb with ⟨hb, hbS⟩ | ⟨hb, _⟩
    · exact phiW_le a b ha3 (by simp [ex3c] at hb; omega) (by rintro rfl; exact hbS ha)
    · exact phiW_le a b ha3 (by simp [ex3c] at hb; omega) (by simp [ex3c] at hb; omega)
  obtain ⟨v03, v13, v01, v10, v20, v23⟩ := vW
  by_cases h0 : 0 ∈ S
  · by_cases h1 : 1 ∈ S
    · refine ⟨(0, 3), (1, 3), ⟨h0, Or.inr ⟨rfl, by simp [ex3c]⟩⟩, ⟨h1, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v03, v13], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v03]
      linarith
    · refine ⟨(0, 1), (0, 3), ⟨h0, Or.inl ⟨by simp [ex3c], h1⟩⟩, ⟨h0, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v01, v03], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v01]
      linarith
  · by_cases h1 : 1 ∈ S
    · refine ⟨(1, 0), (1, 3), ⟨h1, Or.inl ⟨by simp [ex3c], h0⟩⟩, ⟨h1, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
        by simp, by rw [v10, v13], fun e he => ?_⟩
      have h := hle e he
      have h' := c_le e.1
      rw [v10]
      linarith
    · by_cases h2 : 2 ∈ S
      · refine ⟨(2, 0), (2, 3), ⟨h2, Or.inl ⟨by simp [ex3c], h0⟩⟩, ⟨h2, Or.inr ⟨rfl, by simp [ex3c]⟩⟩,
          by simp, by rw [v20, v23], fun e he => ?_⟩
        have h := hle e he
        have he2 : e.1 = 2 := by
          have h3 := hlt e.1 he.1
          have n0 : e.1 ≠ 0 := fun hh => h0 (hh ▸ he.1)
          have n1 : e.1 ≠ 1 := fun hh => h1 (hh ▸ he.1)
          omega
        have hc : c e.1 = -20 := by rw [he2]; simp [c]
        rw [v20]
        linarith
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem psiStar : ex3c.IsPsiStar (-1) := by
  refine ⟨?_, ⟨(0, 1), ⟨by simp, Or.inl (by simp [ex3c])⟩, ?_⟩⟩
  · rintro ⟨a, b⟩ ⟨hab, h | ⟨hb, _, _⟩⟩
    · simp [ex3c] at h hab
      interval_cases b <;> interval_cases a <;> simp [Datum.psiE, psiPair, ex3c] <;> norm_num
    · simp [ex3c] at hb hab
      subst hb
      interval_cases a <;> simp [Datum.psiE, Datum.psiO, ex3c, untopD_one] <;> norm_num
  · simp [Datum.psiE, psiPair, ex3c]

theorem spec : ex3c.IsWeightDatum ∧ Chamber ex3c.n 18 ex3c.u ∧ ex3c.IsPsiStar (-1) := by
  refine ⟨⟨by simp [ex3c], ultra_z, ultra_w, cut_z, cut_w⟩, ⟨by simp [ex3c], ?_⟩, psiStar⟩
  intro j hj hj3
  have hj3' : j < 3 := hj3
  interval_cases j
  simp [ex3c]
  norm_num

end Ex3c

namespace Ex3m

theorem ultra_z : IsUltra 4 ex3m.dz := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dz, ex3m]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dz, ex3m]

theorem ultra_w : IsUltra 4 ex3m.dw := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [Datum.dw, ex3m]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [Datum.dw, ex3m]

theorem phiZ_val (t y : ℕ) : ex3m.phiZ t y = 0 := by
  by_cases ht : t = 1 <;> by_cases hy : y = 3 <;> simp [Datum.phiZ, psiPair, ex3m, ht, hy]

theorem phiW_val (t y : ℕ) : ex3m.phiW t y = 0 := by
  by_cases ht : t = 2 <;> by_cases hy : y = 3 <;> simp [Datum.phiW, psiPair, ex3m, ht, hy]

theorem cut_z (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3m.CutZ S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex3m.termsZ S → ex3m.phiZ e.1 e.2 = 0 := fun e _ => phiZ_val _ _
  by_cases h0 : 0 ∈ S
  · have m0 : (0, 3) ∈ ex3m.termsZ S := ⟨h0, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
    by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · exact ex3m.cutZ_of_const S _ hval _ (2, 3) m0 ⟨h2, Or.inr ⟨rfl, by simp [ex3m]⟩⟩ (by simp)
      · exact ex3m.cutZ_of_const S _ hval _ (0, 2) m0 ⟨h0, Or.inl ⟨by simp [ex3m], h2⟩⟩ (by simp)
    · exact ex3m.cutZ_of_const S _ hval _ (0, 1) m0 ⟨h0, Or.inl ⟨by simp [ex3m], h1⟩⟩ (by simp)
  · by_cases h2 : 2 ∈ S
    · exact ex3m.cutZ_of_const S _ hval (2, 3) (2, 0) ⟨h2, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
        ⟨h2, Or.inl ⟨by simp [ex3m], h0⟩⟩ (by simp)
    · by_cases h1 : 1 ∈ S
      · exact ex3m.cutZ_of_const S _ hval (1, 0) (1, 2) ⟨h1, Or.inl ⟨by simp [ex3m], h0⟩⟩
          ⟨h1, Or.inl ⟨by simp [ex3m], h2⟩⟩ (by simp)
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem cut_w (S : Finset ℕ) (hS : S ⊆ range 3) (hne : S.Nonempty) : ex3m.CutW S := by
  have hlt : ∀ t, t ∈ S → t < 3 := fun t ht => mem_range.mp (hS ht)
  have hval : ∀ e, e ∈ ex3m.termsW S → ex3m.phiW e.1 e.2 = 0 := fun e _ => phiW_val _ _
  by_cases h0 : 0 ∈ S
  · have m0 : (0, 3) ∈ ex3m.termsW S := ⟨h0, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
    by_cases h2 : 2 ∈ S
    · by_cases h1 : 1 ∈ S
      · exact ex3m.cutW_of_const S _ hval _ (1, 3) m0 ⟨h1, Or.inr ⟨rfl, by simp [ex3m]⟩⟩ (by simp)
      · exact ex3m.cutW_of_const S _ hval _ (0, 1) m0 ⟨h0, Or.inl ⟨by simp [ex3m], h1⟩⟩ (by simp)
    · exact ex3m.cutW_of_const S _ hval _ (0, 2) m0 ⟨h0, Or.inl ⟨by simp [ex3m], h2⟩⟩ (by simp)
  · by_cases h1 : 1 ∈ S
    · exact ex3m.cutW_of_const S _ hval (1, 3) (1, 0) ⟨h1, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
        ⟨h1, Or.inl ⟨by simp [ex3m], h0⟩⟩ (by simp)
    · by_cases h2 : 2 ∈ S
      · exact ex3m.cutW_of_const S _ hval (2, 0) (2, 1) ⟨h2, Or.inl ⟨by simp [ex3m], h0⟩⟩
          ⟨h2, Or.inl ⟨by simp [ex3m], h1⟩⟩ (by simp)
      · obtain ⟨t, ht⟩ := hne
        have := hlt t ht
        interval_cases t <;> contradiction

theorem spec :
    ex3m.IsWeightDatum ∧ ¬ex3m.IsEdge (1, 3) ∧ ¬ex3m.IsEdge (2, 3) ∧
    (1, 3) ∉ ex3m.termsZ {1} ∧ (1, 3) ∈ ex3m.termsW {1} ∧
    (2, 3) ∈ ex3m.termsZ {2} ∧ (2, 3) ∉ ex3m.termsW {2} := by
  refine ⟨⟨by simp [ex3m], ultra_z, ultra_w, cut_z, cut_w⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨_, h | ⟨_, hxi, _⟩⟩
    · simp [ex3m] at h
    · simp [ex3m] at hxi
  · rintro ⟨_, h | ⟨_, _, heta⟩⟩
    · simp [ex3m] at h
    · simp [ex3m] at heta
  · rintro ⟨_, h | ⟨_, hxi⟩⟩
    · simp [ex3m] at h
    · simp [ex3m] at hxi
  · exact ⟨by simp, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
  · exact ⟨by simp, Or.inr ⟨rfl, by simp [ex3m]⟩⟩
  · rintro ⟨_, h | ⟨_, heta⟩⟩
    · simp [ex3m] at h
    · simp [ex3m] at heta

end Ex3m

namespace Ex4

theorem ultra_z : IsUltra 4 (fun x y => (ex4z x y : WithTop ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [ex4z]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [ex4z]

theorem ultra_w : IsUltra 4 (fun x y => (ex4w x y : WithTop ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [ex4w]
  · intro x y t hx hy ht hxy hyt hxt
    interval_cases x <;> interval_cases y <;> interval_cases t <;> simp_all [ex4w]

theorem psi_val : ∀ a b, a < b → b < 4 → psiPair ex4u ex4z ex4w a b = 0 := by
  intro a b hab hb
  interval_cases b <;> interval_cases a <;> simp [psiPair, ex4u, ex4z, ex4w] <;> norm_num

theorem top (a b : ℕ) (hab : a < b) (hb : b < 4) : (a, b) ∈ topPairs 4 ex4u ex4z ex4w :=
  ⟨hab, hb, fun c d hcd hd => by rw [psi_val c d hcd hd, psi_val a b hab hb]⟩

theorem nz01 : node 4 (fun x y => (ex4z x y : WithTop ℝ)) (0, 1) = {0, 1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4z] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl | rfl) <;> simp [ex4z]

theorem nz03 : node 4 (fun x y => (ex4z x y : WithTop ℝ)) (0, 3) = {0, 1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4z] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl | rfl) <;> simp [ex4z]

theorem nz12 : node 4 (fun x y => (ex4z x y : WithTop ℝ)) (1, 2) = {1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4z] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl) <;> simp [ex4z]

theorem nz23 : node 4 (fun x y => (ex4z x y : WithTop ℝ)) (2, 3) = {1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4z] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl) <;> simp [ex4z]

theorem nw01 : node 4 (fun x y => (ex4w x y : WithTop ℝ)) (0, 1) = {0, 1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4w] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl | rfl) <;> simp [ex4w]

theorem nw12 : node 4 (fun x y => (ex4w x y : WithTop ℝ)) (1, 2) = {0, 1, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4w] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl | rfl) <;> simp [ex4w]

theorem nw23 : node 4 (fun x y => (ex4w x y : WithTop ℝ)) (2, 3) = {0, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4w] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl) <;> simp [ex4w]

theorem nw03 : node 4 (fun x y => (ex4w x y : WithTop ℝ)) (0, 3) = {0, 2, 3} := by
  ext p
  simp only [node, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hp, h⟩
    interval_cases p <;> simp_all [ex4w] <;> exact absurd h two_not_le_zero
  · rintro (rfl | rfl | rfl) <;> simp [ex4w]

theorem cycle : IsCycle (topPairs 4 ex4u ex4z ex4w) (node 4 fun x y => (ex4z x y : WithTop ℝ))
    (node 4 fun x y => (ex4w x y : WithTop ℝ)) 2
    (fun i => if i = 0 then (0, 1) else (2, 3)) (fun i => if i = 0 then (1, 2) else (0, 3)) where
  pos := by norm_num
  mem_f := by
    intro i hi
    interval_cases i
    · exact top 0 1 (by norm_num) (by norm_num)
    · exact top 2 3 (by norm_num) (by norm_num)
  mem_g := by
    intro i hi
    interval_cases i
    · exact top 1 2 (by norm_num) (by norm_num)
    · exact top 0 3 (by norm_num) (by norm_num)
  adj_w := by
    intro i hi
    interval_cases i
    · show node 4 _ (0, 1) = node 4 _ (1, 2)
      rw [nw01, nw12]
    · show node 4 _ (2, 3) = node 4 _ (0, 3)
      rw [nw23, nw03]
  adj_z := by
    intro i hi
    interval_cases i
    · show node 4 _ (1, 2) = node 4 _ (2, 3)
      rw [nz12, nz23]
    · show node 4 _ (0, 3) = node 4 _ (0, 1)
      rw [nz03, nz01]
  inj_f := by
    intro i j hi hj h
    interval_cases i <;> interval_cases j <;> simp_all
  inj_g := by
    intro i j hi hj h
    interval_cases i <;> interval_cases j <;> simp_all
  ne_fg := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;> simp
  inj_w := by
    intro i j hi hj h
    interval_cases i <;> interval_cases j
    · rfl
    · exact absurd h (by show node 4 _ (0, 1) ≠ node 4 _ (2, 3); rw [nw01, nw23]; decide)
    · exact absurd h (by show node 4 _ (2, 3) ≠ node 4 _ (0, 1); rw [nw01, nw23]; decide)
    · rfl
  inj_z := by
    intro i j hi hj h
    interval_cases i <;> interval_cases j
    · rfl
    · exact absurd h (by show node 4 _ (0, 1) ≠ node 4 _ (2, 3); rw [nz01, nz23]; decide)
    · exact absurd h (by show node 4 _ (2, 3) ≠ node 4 _ (0, 1); rw [nz01, nz23]; decide)
    · rfl

end Ex4
