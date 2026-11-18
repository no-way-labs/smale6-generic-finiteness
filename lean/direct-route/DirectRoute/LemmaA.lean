import DirectRoute.DefsA
import DirectRoute.Cycle

/-!
Lemma A: the weights of a solution of N_n over a valued field form a weight datum; and the bound on
v((X_t − X_l)(Y_t − Y_l)) at a solution whose mass weights lie in a chamber.
-/

open Finset

namespace LA

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℝ))

/-- In a finite sum equal to 0 with a nonzero term, the least valuation is attained by two different
nonzero terms. -/
theorem two_min {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → K) (hsum : ∑ i ∈ s, f i = 0)
    (hne : ∃ i, i ∈ s ∧ f i ≠ 0) :
    ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 ∧ v (f i) = v (f j) ∧
      ∀ k, k ∈ s → v (f i) ≤ v (f k) := by
  obtain ⟨i0, hi0, hf0⟩ := hne
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun k => v (f k)) ⟨i0, hi0⟩
  have hvi : v (f i) ≠ ⊤ := by
    intro h
    have h1 := hmin i0 hi0
    rw [h, top_le_iff] at h1
    exact hf0 ((AddValuation.top_iff v).mp h1)
  have hfi : f i ≠ 0 := (AddValuation.ne_top_iff v).mp hvi
  by_cases hex : ∃ j, j ∈ s ∧ j ≠ i ∧ v (f j) = v (f i)
  · obtain ⟨j, hj, hji, hvj⟩ := hex
    exact ⟨i, hi, j, hj, Ne.symm hji, hfi, (AddValuation.ne_top_iff v).mp (hvj ▸ hvi), hvj.symm, hmin⟩
  · push_neg at hex
    have hlt : ∀ j ∈ s.erase i, v (f i) < v (f j) := by
      intro j hj
      rw [mem_erase] at hj
      exact lt_of_le_of_ne (hmin j hj.2) (Ne.symm (hex j hj.2 hj.1))
    have h1 := AddValuation.map_lt_sum v hvi hlt
    have h2 : ∑ j ∈ s.erase i, f j = -f i := by
      have h3 := Finset.add_sum_erase s f hi
      rw [hsum] at h3
      linear_combination h3
    rw [h2, AddValuation.map_neg] at h1
    exact absurd h1 (lt_irrefl _)

/-- A sum over the ordered pairs of different elements of a set of an antisymmetric function is 0. -/
theorem antisym_sum (S : Finset ℕ) (g : ℕ → ℕ → K) (h : ∀ t, t ∈ S → ∀ l, l ∈ S → g l t = -g t l) :
    ∑ t ∈ S, ∑ l ∈ S.erase t, g t l = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih (fun t ht l hl => h t (mem_insert_of_mem ht) l (mem_insert_of_mem hl))
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have e : ∀ t ∈ S, ∑ l ∈ (insert a S).erase t, g t l = g t a + ∑ l ∈ S.erase t, g t l := by
      intro t ht
      have hta : t ≠ a := fun hh => ha (hh ▸ ht)
      rw [Finset.erase_insert_of_ne (Ne.symm hta), Finset.sum_insert]
      intro hh
      exact ha (Finset.mem_of_mem_erase hh)
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih', add_zero, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l hl
    rw [h a (mem_insert_self a S) l (mem_insert_of_mem hl)]
    ring

variable {n : ℕ} {m X Y : ℕ → K} {Pf : ℕ → ℕ → K}

theorem sol_ne (hsol : IsSolution n m X Y Pf) {t l : ℕ} (ht : t < n) (hl : l < n) (htl : t ≠ l) :
    X t - X l ≠ 0 ∧ Y t - Y l ≠ 0 ∧ Pf t l ≠ 0 := by
  have h := hsol.n1 t l ht hl htl
  refine ⟨?_, ?_, ?_⟩ <;> (intro h0; rw [h0] at h; simp at h)

/-- The real valuation of P_tl: 2 v(P_tl) + ζ_tl + ω_tl = 0. -/
theorem vP (hsol : IsSolution n m X Y Pf) {t l : ℕ} (ht : t < n) (hl : l < n) (htl : t ≠ l) :
    ∃ p : ℝ, v (Pf t l) = (p : WithTop ℝ) ∧
      2 * p + (weights v n m X Y).z t l + (weights v n m X Y).w t l = 0 := by
  obtain ⟨hX, hY, hP⟩ := sol_ne hsol ht hl htl
  have hX' := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hX)
  have hY' := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hY)
  have hP' := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hP)
  refine ⟨(v (Pf t l)).untopD 0, hP'.symm, ?_⟩
  have h := congrArg v (hsol.n1 t l ht hl htl)
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_one, two_nsmul,
    ← hX', ← hY', ← hP'] at h
  have h' : (v (Pf t l)).untopD 0 + (v (Pf t l)).untopD 0 + (v (X t - X l)).untopD 0
      + (v (Y t - Y l)).untopD 0 = 0 := by exact_mod_cast h
  show 2 * (v (Pf t l)).untopD 0 + (v (X t - X l)).untopD 0 + (v (Y t - Y l)).untopD 0 = 0
  linarith

/-- ζ (for the colour W: ω) of the weights is an ultrametric on the n + 1 vertices. -/
theorem ultra_Z (hsol : IsSolution n m X Y Pf) : IsUltra (n + 1) (weights v n m X Y).dz := by
  have hd : ∀ x y, x ≤ n → y ≤ n → x ≠ y → (weights v n m X Y).dz x y
      = v ((if x = n then 0 else X x) - (if y = n then 0 else X y)) := by
    intro x y hx hy hxy
    by_cases hxn : x = n
    · have hyn : y ≠ n := fun hh => hxy (hxn.trans hh.symm)
      simp [Datum.dz, weights, hxn, hyn]
    · by_cases hyn : y = n
      · simp [Datum.dz, weights, hxn, hyn]
      · have hne := (sol_ne hsol (t := x) (l := y) (by omega) (by omega) hxy).1
        have hc := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hne)
        simp only [Datum.dz, weights, hxn, hyn, if_false]
        exact hc
  refine ⟨fun x y hx hy => ?_, fun x y t hx hy ht hxy hyt hxt => ?_⟩
  · by_cases hxy : x = y
    · rw [hxy]
    · rw [hd x y (by omega) (by omega) hxy, hd y x (by omega) (by omega) (Ne.symm hxy)]
      exact AddValuation.map_sub_swap v _ _
  · rw [hd x y (by omega) (by omega) hxy, hd y t (by omega) (by omega) hyt,
      hd x t (by omega) (by omega) hxt]
    have h := AddValuation.map_add v ((if x = n then 0 else X x) - (if y = n then 0 else X y))
      ((if y = n then 0 else X y) - (if t = n then 0 else X t))
    rwa [sub_add_sub_cancel] at h

/-- The cut condition of colour Z at a solution. -/
theorem cut_Z (hn : 2 ≤ n) (hm : ∀ t, t < n → m t ≠ 0) (hsol : IsSolution n m X Y Pf)
    (S : Finset ℕ) (hS : S ⊆ range n) (hSne : S.Nonempty) : (weights v n m X Y).CutZ S := by
  classical
  have hSn : ∀ t, t ∈ S → t < n := fun t ht => mem_range.mp (hS ht)
  have hu : ∀ t, t < n → v (m t) = (((weights v n m X Y).u t : ℝ) : WithTop ℝ) := fun t ht =>
    (D4.coe_untopD ((AddValuation.ne_top_iff v).mpr (hm t ht))).symm
  have hh : ∀ t l, t < n → l < n → t ≠ l →
      v (X t - X l) = (((weights v n m X Y).z t l : ℝ) : WithTop ℝ) := fun t l ht hl htl =>
    (D4.coe_untopD ((AddValuation.ne_top_iff v).mpr (sol_ne hsol ht hl htl).1)).symm
  -- the valuation of the term of a body pair
  have hpair : ∀ t l, t < n → l < n → t ≠ l →
      v (-(m t * m l * Pf t l ^ 3 * (X t - X l)))
        = ((-(weights v n m X Y).phiZ t l : ℝ) : WithTop ℝ) := by
    intro t l ht hl htl
    obtain ⟨p, hp1, hp2⟩ := vP v hsol ht hl htl
    have e3 : (3 : ℕ) • ((p : ℝ) : WithTop ℝ) = ((p + p + p : ℝ) : WithTop ℝ) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
      norm_cast
    rw [AddValuation.map_neg, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul,
      AddValuation.map_pow, hu t ht, hu l hl, hh t l ht hl htl, hp1, e3]
    have ephi : (weights v n m X Y).phiZ t l
        = psiPair (weights v n m X Y).u (weights v n m X Y).z (weights v n m X Y).w t l
          + (weights v n m X Y).w t l := by
      have hln : l ≠ (weights v n m X Y).n := Nat.ne_of_lt hl
      simp only [Datum.phiZ, hln, if_false]
    have e : (weights v n m X Y).u t + (weights v n m X Y).u l + (p + p + p)
        + (weights v n m X Y).z t l = -(weights v n m X Y).phiZ t l := by
      rw [ephi]
      unfold psiPair
      linarith
    rw [← e]
    norm_cast
  -- the valuation of the term of an O-edge
  have hO : ∀ t, t < n → X t ≠ 0 →
      v (m t * X t) = ((-(weights v n m X Y).phiZ t n : ℝ) : WithTop ℝ) := by
    intro t ht hXt
    have hc := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hXt)
    rw [AddValuation.map_mul, hu t ht, ← hc]
    have ephi : (weights v n m X Y).phiZ t n
        = -(weights v n m X Y).u t - (v (X t)).untopD 0 := by
      have hnn : n = (weights v n m X Y).n := rfl
      simp only [Datum.phiZ, ← hnn, if_true]
      rfl
    rw [ephi]
    norm_cast
    ring
  -- the cut identity
  have hid : ∑ t ∈ S, m t * X t
      - ∑ t ∈ S, ∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (X t - X l) = 0 := by
    have h1 : ∀ t ∈ S, m t * X t
        = ∑ l ∈ S.erase t, m t * m l * Pf t l ^ 3 * (X t - X l)
          + ∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (X t - X l) := by
      intro t ht
      have h2 := hsol.n2 t (hSn t ht)
      have h3 : (range n).erase t = S.erase t ∪ (range n \ S) := by
        ext l
        simp only [mem_erase, mem_range, mem_union, mem_sdiff]
        constructor
        · rintro ⟨h4, h5⟩
          by_cases h6 : l ∈ S
          · exact Or.inl ⟨h4, h6⟩
          · exact Or.inr ⟨h5, h6⟩
        · rintro (⟨h4, h5⟩ | ⟨h4, h5⟩)
          · exact ⟨h4, hSn l h5⟩
          · exact ⟨fun hh => h5 (hh ▸ ht), h4⟩
      have h4 : Disjoint (S.erase t) (range n \ S) := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        exact (mem_sdiff.mp hl').2 (Finset.mem_of_mem_erase hl)
      rw [h3, Finset.sum_union h4] at h2
      calc m t * X t = m t * (∑ l ∈ S.erase t, m l * Pf t l ^ 3 * (X t - X l)
            + ∑ l ∈ range n \ S, m l * Pf t l ^ 3 * (X t - X l)) := by rw [← h2]
        _ = _ := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
            congr 1 <;> (apply Finset.sum_congr rfl; intro l _; ring)
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have h5 := antisym_sum S (fun t l => m t * m l * Pf t l ^ 3 * (X t - X l)) (by
      intro t ht l hl
      rw [hsol.psymm l t (hSn l hl) (hSn t ht)]
      ring)
    rw [h5]
    ring
  -- the terms, indexed by pairs
  have hT : ∀ e : ℕ × ℕ, e ∈ S ×ˢ (range n \ S) ∪ S.image (fun t => (t, n)) ↔
      e.1 ∈ S ∧ ((e.2 < n ∧ e.2 ∉ S) ∨ e.2 = n) := by
    rintro ⟨t, l⟩
    simp only [mem_union, mem_product, mem_sdiff, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨a, h1, h2, h3⟩)
      · exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
      · exact ⟨h2 ▸ h1, Or.inr h3.symm⟩
    · rintro ⟨h1, ⟨h2, h3⟩ | h2⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨t, h1, rfl, h2.symm⟩
  generalize hTdef : S ×ˢ (range n \ S) ∪ S.image (fun t => (t, n)) = T at hT
  have hsum : ∑ e ∈ T, (if e.2 = n then m e.1 * X e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (X e.1 - X e.2))) = 0 := by
    rw [← hTdef, Finset.sum_union, Finset.sum_product, Finset.sum_image]
    · have h1 : ∀ t ∈ S, ∑ l ∈ range n \ S, (if (t, l).2 = n then m (t, l).1 * X (t, l).1
          else -(m (t, l).1 * m (t, l).2 * Pf (t, l).1 (t, l).2 ^ 3 * (X (t, l).1 - X (t, l).2)))
          = -∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (X t - X l) := by
        intro t _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        have hln : l ≠ n := Nat.ne_of_lt (mem_range.mp (mem_sdiff.mp hl).1)
        simp only [hln, if_false]
      rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
      simp only [if_true]
      linear_combination hid
    · intro a _ b _ hab
      exact congrArg Prod.fst hab
    · rw [Finset.disjoint_left]
      rintro ⟨t, l⟩ h1 h2
      simp only [mem_product, mem_sdiff, mem_range] at h1
      simp only [mem_image, Prod.mk.injEq] at h2
      obtain ⟨a, _, _, h3⟩ := h2
      omega
  -- a term of the cut that is not 0, and its valuation
  have hterm : ∀ e : ℕ × ℕ, e ∈ (weights v n m X Y).termsZ S →
      e ∈ T ∧ v (if e.2 = n then m e.1 * X e.1
          else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (X e.1 - X e.2)))
        = ((-(weights v n m X Y).phiZ e.1 e.2 : ℝ) : WithTop ℝ) := by
    rintro ⟨t, l⟩ ⟨htS, hl⟩
    have htS' : t ∈ S := htS
    have htn := hSn t htS'
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : l < n := h1
      have h2' : l ∉ S := h2
      have hln : l ≠ n := Nat.ne_of_lt h1'
      have htl : t ≠ l := fun hh => h2' (hh ▸ htS')
      refine ⟨(hT (t, l)).mpr ⟨htS', Or.inl ⟨h1', h2'⟩⟩, ?_⟩
      simp only [hln, if_false]
      exact hpair t l htn h1' htl
    · have h1' : l = n := h1
      have h2' : v (X t) ≠ ⊤ := h2
      subst h1'
      refine ⟨(hT (t, l)).mpr ⟨htS', Or.inr rfl⟩, ?_⟩
      simp only [if_true]
      exact hO t htn ((AddValuation.ne_top_iff v).mp h2')
  have hnz : ∀ e : ℕ × ℕ, e ∈ T → (if e.2 = n then m e.1 * X e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (X e.1 - X e.2))) ≠ 0 →
      e ∈ (weights v n m X Y).termsZ S := by
    rintro ⟨t, l⟩ he hne
    obtain ⟨h1, h2⟩ := (hT (t, l)).mp he
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · right
      refine ⟨h2, ?_⟩
      have h2' : l = n := h2
      subst h2'
      simp only [if_true] at hne
      show v (X t) ≠ ⊤
      rw [AddValuation.ne_top_iff]
      intro h0
      rw [h0, mul_zero] at hne
      exact hne rfl
  -- a nonzero term exists
  have hex : ∃ e, e ∈ T ∧ (if e.2 = n then m e.1 * X e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (X e.1 - X e.2))) ≠ 0 := by
    obtain ⟨t, ht⟩ := hSne
    have htn := hSn t ht
    by_cases hall : ∃ l, l < n ∧ l ∉ S
    · obtain ⟨l, hl, hlS⟩ := hall
      have htl : t ≠ l := fun hh => hlS (hh ▸ ht)
      have hmem := (hterm (t, l) ⟨ht, Or.inl ⟨hl, hlS⟩⟩)
      refine ⟨(t, l), hmem.1, ?_⟩
      intro h0
      have h1 := hmem.2
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.coe_ne_top h1.symm
    · push_neg at hall
      -- S is the set of all bodies; one of X_0, X_1 is not 0
      have h01 := (sol_ne hsol (t := 0) (l := 1) (by omega) (by omega) (by norm_num)).1
      have hx : ∃ s, s < n ∧ X s ≠ 0 := by
        by_cases h0 : X 0 = 0
        · refine ⟨1, by omega, fun h1 => h01 ?_⟩
          rw [h0, h1, sub_zero]
        · exact ⟨0, by omega, h0⟩
      obtain ⟨s, hs, hXs⟩ := hx
      have hsS : s ∈ S := hall s hs
      have hmem := hterm (s, n) ⟨hsS, Or.inr ⟨rfl, (AddValuation.ne_top_iff v).mpr hXs⟩⟩
      refine ⟨(s, n), hmem.1, ?_⟩
      intro h0
      have h1 := hmem.2
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.coe_ne_top h1.symm
  obtain ⟨e₁, m₁, e₂, m₂, hne, z₁, z₂, heq, hmin⟩ := two_min v T _ hsum hex
  have t₁ := hnz e₁ m₁ z₁
  have t₂ := hnz e₂ m₂ z₂
  refine ⟨e₁, e₂, t₁, t₂, hne, ?_, ?_⟩
  · rw [(hterm e₁ t₁).2, (hterm e₂ t₂).2] at heq
    have h1 : -(weights v n m X Y).phiZ e₁.1 e₁.2 = -(weights v n m X Y).phiZ e₂.1 e₂.2 := by
      exact_mod_cast heq
    linarith
  · intro e he
    have h1 := hmin e (hterm e he).1
    rw [(hterm e₁ t₁).2, (hterm e he).2] at h1
    have h2 : -(weights v n m X Y).phiZ e₁.1 e₁.2 ≤ -(weights v n m X Y).phiZ e.1 e.2 := by
      exact_mod_cast h1
    linarith

/-- ζ (for the colour W: ω) of the weights is an ultrametric on the n + 1 vertices. -/
theorem ultra_W (hsol : IsSolution n m X Y Pf) : IsUltra (n + 1) (weights v n m X Y).dw := by
  have hd : ∀ x y, x ≤ n → y ≤ n → x ≠ y → (weights v n m X Y).dw x y
      = v ((if x = n then 0 else Y x) - (if y = n then 0 else Y y)) := by
    intro x y hx hy hxy
    by_cases hxn : x = n
    · have hyn : y ≠ n := fun hh => hxy (hxn.trans hh.symm)
      simp [Datum.dw, weights, hxn, hyn]
    · by_cases hyn : y = n
      · simp [Datum.dw, weights, hxn, hyn]
      · have hne := (sol_ne hsol (t := x) (l := y) (by omega) (by omega) hxy).2.1
        have hc := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hne)
        simp only [Datum.dw, weights, hxn, hyn, if_false]
        exact hc
  refine ⟨fun x y hx hy => ?_, fun x y t hx hy ht hxy hyt hxt => ?_⟩
  · by_cases hxy : x = y
    · rw [hxy]
    · rw [hd x y (by omega) (by omega) hxy, hd y x (by omega) (by omega) (Ne.symm hxy)]
      exact AddValuation.map_sub_swap v _ _
  · rw [hd x y (by omega) (by omega) hxy, hd y t (by omega) (by omega) hyt,
      hd x t (by omega) (by omega) hxt]
    have h := AddValuation.map_add v ((if x = n then 0 else Y x) - (if y = n then 0 else Y y))
      ((if y = n then 0 else Y y) - (if t = n then 0 else Y t))
    rwa [sub_add_sub_cancel] at h

/-- The cut condition of colour W at a solution. -/
theorem cut_W (hn : 2 ≤ n) (hm : ∀ t, t < n → m t ≠ 0) (hsol : IsSolution n m X Y Pf)
    (S : Finset ℕ) (hS : S ⊆ range n) (hSne : S.Nonempty) : (weights v n m X Y).CutW S := by
  classical
  have hSn : ∀ t, t ∈ S → t < n := fun t ht => mem_range.mp (hS ht)
  have hu : ∀ t, t < n → v (m t) = (((weights v n m X Y).u t : ℝ) : WithTop ℝ) := fun t ht =>
    (D4.coe_untopD ((AddValuation.ne_top_iff v).mpr (hm t ht))).symm
  have hh : ∀ t l, t < n → l < n → t ≠ l →
      v (Y t - Y l) = (((weights v n m X Y).w t l : ℝ) : WithTop ℝ) := fun t l ht hl htl =>
    (D4.coe_untopD ((AddValuation.ne_top_iff v).mpr (sol_ne hsol ht hl htl).2.1)).symm
  -- the valuation of the term of a body pair
  have hpair : ∀ t l, t < n → l < n → t ≠ l →
      v (-(m t * m l * Pf t l ^ 3 * (Y t - Y l)))
        = ((-(weights v n m X Y).phiW t l : ℝ) : WithTop ℝ) := by
    intro t l ht hl htl
    obtain ⟨p, hp1, hp2⟩ := vP v hsol ht hl htl
    have e3 : (3 : ℕ) • ((p : ℝ) : WithTop ℝ) = ((p + p + p : ℝ) : WithTop ℝ) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
      norm_cast
    rw [AddValuation.map_neg, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul,
      AddValuation.map_pow, hu t ht, hu l hl, hh t l ht hl htl, hp1, e3]
    have ephi : (weights v n m X Y).phiW t l
        = psiPair (weights v n m X Y).u (weights v n m X Y).z (weights v n m X Y).w t l
          + (weights v n m X Y).z t l := by
      have hln : l ≠ (weights v n m X Y).n := Nat.ne_of_lt hl
      simp only [Datum.phiW, hln, if_false]
    have e : (weights v n m X Y).u t + (weights v n m X Y).u l + (p + p + p)
        + (weights v n m X Y).w t l = -(weights v n m X Y).phiW t l := by
      rw [ephi]
      unfold psiPair
      linarith
    rw [← e]
    norm_cast
  -- the valuation of the term of an O-edge
  have hO : ∀ t, t < n → Y t ≠ 0 →
      v (m t * Y t) = ((-(weights v n m X Y).phiW t n : ℝ) : WithTop ℝ) := by
    intro t ht hXt
    have hc := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hXt)
    rw [AddValuation.map_mul, hu t ht, ← hc]
    have ephi : (weights v n m X Y).phiW t n
        = -(weights v n m X Y).u t - (v (Y t)).untopD 0 := by
      have hnn : n = (weights v n m X Y).n := rfl
      simp only [Datum.phiW, ← hnn, if_true]
      rfl
    rw [ephi]
    norm_cast
    ring
  -- the cut identity
  have hid : ∑ t ∈ S, m t * Y t
      - ∑ t ∈ S, ∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (Y t - Y l) = 0 := by
    have h1 : ∀ t ∈ S, m t * Y t
        = ∑ l ∈ S.erase t, m t * m l * Pf t l ^ 3 * (Y t - Y l)
          + ∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (Y t - Y l) := by
      intro t ht
      have h2 := hsol.n3 t (hSn t ht)
      have h3 : (range n).erase t = S.erase t ∪ (range n \ S) := by
        ext l
        simp only [mem_erase, mem_range, mem_union, mem_sdiff]
        constructor
        · rintro ⟨h4, h5⟩
          by_cases h6 : l ∈ S
          · exact Or.inl ⟨h4, h6⟩
          · exact Or.inr ⟨h5, h6⟩
        · rintro (⟨h4, h5⟩ | ⟨h4, h5⟩)
          · exact ⟨h4, hSn l h5⟩
          · exact ⟨fun hh => h5 (hh ▸ ht), h4⟩
      have h4 : Disjoint (S.erase t) (range n \ S) := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        exact (mem_sdiff.mp hl').2 (Finset.mem_of_mem_erase hl)
      rw [h3, Finset.sum_union h4] at h2
      calc m t * Y t = m t * (∑ l ∈ S.erase t, m l * Pf t l ^ 3 * (Y t - Y l)
            + ∑ l ∈ range n \ S, m l * Pf t l ^ 3 * (Y t - Y l)) := by rw [← h2]
        _ = _ := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
            congr 1 <;> (apply Finset.sum_congr rfl; intro l _; ring)
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have h5 := antisym_sum S (fun t l => m t * m l * Pf t l ^ 3 * (Y t - Y l)) (by
      intro t ht l hl
      rw [hsol.psymm l t (hSn l hl) (hSn t ht)]
      ring)
    rw [h5]
    ring
  -- the terms, indexed by pairs
  have hT : ∀ e : ℕ × ℕ, e ∈ S ×ˢ (range n \ S) ∪ S.image (fun t => (t, n)) ↔
      e.1 ∈ S ∧ ((e.2 < n ∧ e.2 ∉ S) ∨ e.2 = n) := by
    rintro ⟨t, l⟩
    simp only [mem_union, mem_product, mem_sdiff, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨a, h1, h2, h3⟩)
      · exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
      · exact ⟨h2 ▸ h1, Or.inr h3.symm⟩
    · rintro ⟨h1, ⟨h2, h3⟩ | h2⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨t, h1, rfl, h2.symm⟩
  generalize hTdef : S ×ˢ (range n \ S) ∪ S.image (fun t => (t, n)) = T at hT
  have hsum : ∑ e ∈ T, (if e.2 = n then m e.1 * Y e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (Y e.1 - Y e.2))) = 0 := by
    rw [← hTdef, Finset.sum_union, Finset.sum_product, Finset.sum_image]
    · have h1 : ∀ t ∈ S, ∑ l ∈ range n \ S, (if (t, l).2 = n then m (t, l).1 * Y (t, l).1
          else -(m (t, l).1 * m (t, l).2 * Pf (t, l).1 (t, l).2 ^ 3 * (Y (t, l).1 - Y (t, l).2)))
          = -∑ l ∈ range n \ S, m t * m l * Pf t l ^ 3 * (Y t - Y l) := by
        intro t _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        have hln : l ≠ n := Nat.ne_of_lt (mem_range.mp (mem_sdiff.mp hl).1)
        simp only [hln, if_false]
      rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
      simp only [if_true]
      linear_combination hid
    · intro a _ b _ hab
      exact congrArg Prod.fst hab
    · rw [Finset.disjoint_left]
      rintro ⟨t, l⟩ h1 h2
      simp only [mem_product, mem_sdiff, mem_range] at h1
      simp only [mem_image, Prod.mk.injEq] at h2
      obtain ⟨a, _, _, h3⟩ := h2
      omega
  -- a term of the cut that is not 0, and its valuation
  have hterm : ∀ e : ℕ × ℕ, e ∈ (weights v n m X Y).termsW S →
      e ∈ T ∧ v (if e.2 = n then m e.1 * Y e.1
          else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (Y e.1 - Y e.2)))
        = ((-(weights v n m X Y).phiW e.1 e.2 : ℝ) : WithTop ℝ) := by
    rintro ⟨t, l⟩ ⟨htS, hl⟩
    have htS' : t ∈ S := htS
    have htn := hSn t htS'
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : l < n := h1
      have h2' : l ∉ S := h2
      have hln : l ≠ n := Nat.ne_of_lt h1'
      have htl : t ≠ l := fun hh => h2' (hh ▸ htS')
      refine ⟨(hT (t, l)).mpr ⟨htS', Or.inl ⟨h1', h2'⟩⟩, ?_⟩
      simp only [hln, if_false]
      exact hpair t l htn h1' htl
    · have h1' : l = n := h1
      have h2' : v (Y t) ≠ ⊤ := h2
      subst h1'
      refine ⟨(hT (t, l)).mpr ⟨htS', Or.inr rfl⟩, ?_⟩
      simp only [if_true]
      exact hO t htn ((AddValuation.ne_top_iff v).mp h2')
  have hnz : ∀ e : ℕ × ℕ, e ∈ T → (if e.2 = n then m e.1 * Y e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (Y e.1 - Y e.2))) ≠ 0 →
      e ∈ (weights v n m X Y).termsW S := by
    rintro ⟨t, l⟩ he hne
    obtain ⟨h1, h2⟩ := (hT (t, l)).mp he
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · right
      refine ⟨h2, ?_⟩
      have h2' : l = n := h2
      subst h2'
      simp only [if_true] at hne
      show v (Y t) ≠ ⊤
      rw [AddValuation.ne_top_iff]
      intro h0
      rw [h0, mul_zero] at hne
      exact hne rfl
  -- a nonzero term exists
  have hex : ∃ e, e ∈ T ∧ (if e.2 = n then m e.1 * Y e.1
      else -(m e.1 * m e.2 * Pf e.1 e.2 ^ 3 * (Y e.1 - Y e.2))) ≠ 0 := by
    obtain ⟨t, ht⟩ := hSne
    have htn := hSn t ht
    by_cases hall : ∃ l, l < n ∧ l ∉ S
    · obtain ⟨l, hl, hlS⟩ := hall
      have htl : t ≠ l := fun hh => hlS (hh ▸ ht)
      have hmem := (hterm (t, l) ⟨ht, Or.inl ⟨hl, hlS⟩⟩)
      refine ⟨(t, l), hmem.1, ?_⟩
      intro h0
      have h1 := hmem.2
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.coe_ne_top h1.symm
    · push_neg at hall
      -- S is the set of all bodies; one of X_0, X_1 is not 0
      have h01 := (sol_ne hsol (t := 0) (l := 1) (by omega) (by omega) (by norm_num)).2.1
      have hx : ∃ s, s < n ∧ Y s ≠ 0 := by
        by_cases h0 : Y 0 = 0
        · refine ⟨1, by omega, fun h1 => h01 ?_⟩
          rw [h0, h1, sub_zero]
        · exact ⟨0, by omega, h0⟩
      obtain ⟨s, hs, hXs⟩ := hx
      have hsS : s ∈ S := hall s hs
      have hmem := hterm (s, n) ⟨hsS, Or.inr ⟨rfl, (AddValuation.ne_top_iff v).mpr hXs⟩⟩
      refine ⟨(s, n), hmem.1, ?_⟩
      intro h0
      have h1 := hmem.2
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.coe_ne_top h1.symm
  obtain ⟨e₁, m₁, e₂, m₂, hne, z₁, z₂, heq, hmin⟩ := two_min v T _ hsum hex
  have t₁ := hnz e₁ m₁ z₁
  have t₂ := hnz e₂ m₂ z₂
  refine ⟨e₁, e₂, t₁, t₂, hne, ?_, ?_⟩
  · rw [(hterm e₁ t₁).2, (hterm e₂ t₂).2] at heq
    have h1 : -(weights v n m X Y).phiW e₁.1 e₁.2 = -(weights v n m X Y).phiW e₂.1 e₂.2 := by
      exact_mod_cast heq
    linarith
  · intro e he
    have h1 := hmin e (hterm e he).1
    rw [(hterm e₁ t₁).2, (hterm e he).2] at h1
    have h2 : -(weights v n m X Y).phiW e₁.1 e₁.2 ≤ -(weights v n m X Y).phiW e.1 e.2 := by
      exact_mod_cast h1
    linarith

end LA

/-- Lemma A. -/
theorem lemmaA_proof {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) : (weights v n m X Y).IsWeightDatum :=
  ⟨hn, LA.ultra_Z v hsol, LA.ultra_W v hsol, LA.cut_Z v hn hm hsol, LA.cut_W v hn hm hsol⟩

/-- The bound on v((X_t − X_l)(Y_t − Y_l)) at a solution over a chamber vector. -/
theorem solution_bound_proof {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (m X Y : ℕ → K) (Pf : ℕ → ℕ → K) (hm : ∀ t, t < n → m t ≠ 0)
    (hsol : IsSolution n m X Y Pf) (τ : ℝ) (hτ : 2 * (n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber n τ fun t => (v (m t)).untopD 0) (t l : ℕ) (htl : t < l) (hl : l < n) :
    v ((X t - X l) * (Y t - Y l))
      ≤ ((2 * (2 * (n : ℝ) - 1) * (∑ j ∈ range n, |(v (m j)).untopD 0|) / 3
          + 2 * (v (m t)).untopD 0 + 2 * (v (m l)).untopD 0 : ℝ) : WithTop ℝ) := by
  have hD := lemmaA_proof v n hn m X Y Pf hm hsol
  have hb := collision_bound_proof (weights v n m X Y) τ hD hτ hu t l htl hl
  obtain ⟨hX, hY, _⟩ := LA.sol_ne hsol (lt_trans htl hl) hl (Nat.ne_of_lt htl)
  have hX' := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hX)
  have hY' := D4.coe_untopD ((AddValuation.ne_top_iff v).mpr hY)
  rw [AddValuation.map_mul, ← hX', ← hY']
  have hb' : (v (X t - X l)).untopD 0 + (v (Y t - Y l)).untopD 0
      ≤ 2 * (2 * (n : ℝ) - 1) * (∑ j ∈ range n, |(v (m j)).untopD 0|) / 3
        + 2 * (v (m t)).untopD 0 + 2 * (v (m l)).untopD 0 := hb
  exact_mod_cast hb'
