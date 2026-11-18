import DirectRoute.LemmaC

/-!
Theorem D4, the relation (T4): on every simple cycle of B, N Ψ* + q·u = 0 and N ≠ 0.
Steps 2, 3 and 4 of the proof of the brief. Step 3 uses the cycle lemma in the form `LC.Setup.contra`,
which needs only the heights of the nodes; so the nodes of the trees on the bodies are not compared with
the nodes of the trees on the n + 1 vertices.
-/

open Finset

namespace D4

/-! ### Trees with values in `WithTop ℝ` -/

theorem mem_node {N : ℕ} {d : ℕ → ℕ → WithTop ℝ} {e : ℕ × ℕ} {p : ℕ} :
    p ∈ node N d e ↔ p < N ∧ (p = e.1 ∨ d e.1 e.2 ≤ d e.1 p) := by
  simp [node]

/-- Two different points of a node are at least as high as the node. -/
theorem node_pair {N : ℕ} {d : ℕ → ℕ → WithTop ℝ} (h : IsUltra N d) {a b p p' : ℕ} (ha : a < N)
    (hp : p ∈ node N d (a, b)) (hp' : p' ∈ node N d (a, b)) (hne : p ≠ p') : d a b ≤ d p p' := by
  rw [mem_node] at hp hp'
  obtain ⟨hpn, hp⟩ := hp
  obtain ⟨hpn', hp'⟩ := hp'
  simp only at hp hp'
  by_cases hpa : p = a
  · subst hpa
    rcases hp' with rfl | hp'
    · exact absurd rfl hne
    · exact hp'
  · by_cases hpa' : p' = a
    · subst hpa'
      rcases hp with rfl | hp
      · exact absurd rfl hne
      · rw [h.1 p p' hpn hpn']
        exact hp
    · have h1 : d a b ≤ d a p := by
        rcases hp with rfl | hp
        · exact absurd rfl hpa
        · exact hp
      have h2 : d a b ≤ d a p' := by
        rcases hp' with rfl | hp'
        · exact absurd rfl hpa'
        · exact hp'
      have h3 := h.2 p a p' hpn ha hpn' hpa (Ne.symm hpa') hne
      rw [h.1 p a hpn ha] at h3
      exact le_trans (le_min h1 h2) h3

/-- Two pairs with the same node have the same height. -/
theorem node_height_eq {N : ℕ} {d : ℕ → ℕ → WithTop ℝ} (h : IsUltra N d) {a b a' b' : ℕ}
    (ha : a < N) (hb : b < N) (ha' : a' < N) (hb' : b' < N) (hab : a ≠ b) (hab' : a' ≠ b')
    (heq : node N d (a, b) = node N d (a', b')) : d a b = d a' b' := by
  have m1 : a ∈ node N d (a, b) := mem_node.mpr ⟨ha, Or.inl rfl⟩
  have m2 : b ∈ node N d (a, b) := mem_node.mpr ⟨hb, Or.inr le_rfl⟩
  have m1' : a' ∈ node N d (a', b') := mem_node.mpr ⟨ha', Or.inl rfl⟩
  have m2' : b' ∈ node N d (a', b') := mem_node.mpr ⟨hb', Or.inr le_rfl⟩
  apply le_antisymm
  · rw [← heq] at m1' m2'
    exact node_pair h ha m1' m2' hab'
  · rw [heq] at m1 m2
    exact node_pair h ha' m1 m2 hab

/-! ### The real heights of an edge -/

/-- The height of an edge in ζ, as a real number. -/
def zh (D : Datum) (e : ℕ × ℕ) : ℝ := if e.2 = D.n then (D.xi e.1).untopD 0 else D.z e.1 e.2

/-- The height of an edge in ω, as a real number. -/
def wh (D : Datum) (e : ℕ × ℕ) : ℝ := if e.2 = D.n then (D.eta e.1).untopD 0 else D.w e.1 e.2

theorem coe_untopD {x : WithTop ℝ} (hx : x ≠ ⊤) : ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
  obtain ⟨v, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  simp

theorem dz_body (D : Datum) {x y : ℕ} (hx : x < D.n) (hy : y < D.n) : D.dz x y = (D.z x y : WithTop ℝ) := by
  simp [Datum.dz, Nat.ne_of_lt hx, Nat.ne_of_lt hy]

theorem dw_body (D : Datum) {x y : ℕ} (hx : x < D.n) (hy : y < D.n) : D.dw x y = (D.w x y : WithTop ℝ) := by
  simp [Datum.dw, Nat.ne_of_lt hx, Nat.ne_of_lt hy]

theorem dz_eq (D : Datum) {e : ℕ × ℕ} (he : D.IsEdge e) : D.dz e.1 e.2 = (zh D e : WithTop ℝ) := by
  obtain ⟨h1, h2 | ⟨h2, hxi, _⟩⟩ := he
  · rw [dz_body D (lt_trans h1 h2) h2]
    simp [zh, Nat.ne_of_lt h2]
  · have h3 : e.1 ≠ D.n := by omega
    simp [Datum.dz, zh, h2, h3, coe_untopD hxi]

theorem dw_eq (D : Datum) {e : ℕ × ℕ} (he : D.IsEdge e) : D.dw e.1 e.2 = (wh D e : WithTop ℝ) := by
  obtain ⟨h1, h2 | ⟨h2, _, heta⟩⟩ := he
  · rw [dw_body D (lt_trans h1 h2) h2]
    simp [wh, Nat.ne_of_lt h2]
  · have h3 : e.1 ≠ D.n := by omega
    simp [Datum.dw, wh, h2, h3, coe_untopD heta]

theorem edge_le (D : Datum) {e : ℕ × ℕ} (he : D.IsEdge e) : e.1 < e.2 ∧ e.2 ≤ D.n := by
  obtain ⟨h1, h2 | ⟨h2, _, _⟩⟩ := he
  · exact ⟨h1, h2.le⟩
  · exact ⟨h1, h2.le⟩

/-- The sum of the coefficients `inc` of an edge with the weights. -/
theorem sum_inc_mul (D : Datum) {e : ℕ × ℕ} (he : D.IsEdge e) :
    ∑ k ∈ range D.n, (inc D.n e k : ℝ) * D.u k
      = if e.2 < D.n then 2 * (D.u e.1 + D.u e.2) else -D.u e.1 := by
  obtain ⟨h1, h2 | ⟨h2, _, _⟩⟩ := he
  · have key : ∀ k, (inc D.n e k : ℝ) * D.u k = 2 * ((LC.on e k : ℝ) * D.u k) := by
      intro k
      unfold inc LC.on
      by_cases hk : e.1 = k ∨ e.2 = k <;> simp [h2, hk]
    simp only [key, ← Finset.mul_sum, LC.sum_on_mul h1 h2, h2, if_true]
  · have h3 : ¬e.2 < D.n := by omega
    have h4 : e.1 < D.n := by omega
    have key : ∀ k, (inc D.n e k : ℝ) * D.u k = if e.1 = k then -D.u k else 0 := by
      intro k
      unfold inc
      by_cases hk : e.1 = k <;> simp [h3, hk]
    simp only [key, Finset.sum_ite_eq, mem_range, h4, h3, if_true, if_false]

/-- ζ_e + ω_e in terms of Ψ* and the weights (Step 2 of the brief). -/
theorem val_eq (D : Datum) {P : ℝ} {e : ℕ × ℕ} (he : e ∈ D.Estar P) :
    zh D e + wh D e
      = (3 * (if e.2 < D.n then (1 : ℝ) else 0) - 1) * P + ∑ k ∈ range D.n, (inc D.n e k : ℝ) * D.u k := by
  obtain ⟨hedge, hpsi⟩ := he
  rw [sum_inc_mul D hedge]
  obtain ⟨h1, h2 | ⟨h2, _, _⟩⟩ := hedge
  · have h3 : e.2 ≠ D.n := Nat.ne_of_lt h2
    simp only [Datum.psiE, h3, if_false] at hpsi
    unfold psiPair at hpsi
    simp only [zh, wh, h3, h2, if_true, if_false]
    linarith
  · have h3 : ¬e.2 < D.n := by omega
    simp only [Datum.psiE, h2, if_true, Datum.psiO] at hpsi
    simp only [zh, wh, h2, lt_irrefl, if_true, if_false]
    linarith

/-- A sum over one turn of a cycle does not change under the shift of the index. -/
theorem sum_shift_mod (r : ℕ) (hr : 0 < r) (h : ℕ → ℝ) :
    ∑ i ∈ range r, h ((i + 1) % r) = ∑ i ∈ range r, h i := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.mod_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [Nat.mod_eq_of_lt (by omega)]

section cycle

variable {D : Datum} {P : ℝ} {r : ℕ} {f g : ℕ → ℕ × ℕ}

theorem adj_wh (hD : D.IsWeightDatum)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) {i : ℕ} (hi : i < r) :
    wh D (f i) = wh D (g i) := by
  have ef := (hc.mem_f i hi).1
  have eg := (hc.mem_g i hi).1
  have lf := edge_le D ef
  have lg := edge_le D eg
  have h := node_height_eq hD.ultra_w (a := (f i).1) (b := (f i).2) (a' := (g i).1) (b' := (g i).2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (hc.adj_w i hi)
  rw [dw_eq D ef, dw_eq D eg] at h
  exact_mod_cast h

theorem adj_zh (hD : D.IsWeightDatum)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) {i : ℕ} (hi : i < r) :
    zh D (g i) = zh D (f ((i + 1) % r)) := by
  have hi' : (i + 1) % r < r := Nat.mod_lt _ (by omega)
  have ef := (hc.mem_f _ hi').1
  have eg := (hc.mem_g i hi).1
  have lf := edge_le D ef
  have lg := edge_le D eg
  have h := node_height_eq hD.ultra_z (a := (g i).1) (b := (g i).2) (a' := (f ((i + 1) % r)).1)
    (b' := (f ((i + 1) % r)).2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hc.adj_z i hi)
  rw [dz_eq D eg, dz_eq D ef] at h
  exact_mod_cast h

/-- Step 2: the relation N Ψ* + q·u = 0. -/
theorem relation (hD : D.IsWeightDatum)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
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
      rw [adj_zh hD hc hi, adj_wh hD hc hi]
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
theorem has_O {τ : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber D.n τ D.u)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
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
      have h := adj_wh hD hc (hmod i)
      simp only [wh, (hcon _ (hmod i)).1, (hcon _ (hmod i)).2, if_false] at h
      exact h
    · intro i
      have h := adj_zh hD hc (hmod i)
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

end cycle

/-! ### Step 4: N ≠ 0 -/

/-- Lemma B in the form used twice: a vector of integers with sum 0, bounded entries and q·u = 0 over a
chamber vector is 0. -/
theorem lemmaB_apply {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (q : ℕ → ℤ)
    (B : ℝ) (hB : ∀ k, k < n → |(q k : ℝ)| ≤ B) (hBτ : (n : ℝ) * B ≤ τ + 1)
    (hsum : ∑ k ∈ range n, q k = 0) (hqu : ∑ k ∈ range n, (q k : ℝ) * u k = 0) :
    ∀ k, k < n → q k = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k0, hk0, hq0⟩ := hcon
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB k0 hk0)
  have hmP : q (Nat.findGreatest (fun k => q k ≠ 0) (n - 1)) ≠ 0 :=
    Nat.findGreatest_spec (P := fun k => q k ≠ 0) (by omega : k0 ≤ n - 1) hq0
  have hmle : Nat.findGreatest (fun k => q k ≠ 0) (n - 1) ≤ n - 1 := Nat.findGreatest_le _
  have hgt : ∀ k, Nat.findGreatest (fun k => q k ≠ 0) (n - 1) < k → k < n → q k = 0 := by
    intro k hk hkn
    by_contra h
    exact Nat.findGreatest_is_greatest hk (by omega) h
  generalize Nat.findGreatest (fun k => q k ≠ 0) (n - 1) = m at hmP hmle hgt
  have hsub : range (m + 1) ⊆ range n := by
    intro x hx
    rw [mem_range] at hx ⊢
    omega
  have hsum' : ∑ j ∈ range (m + 1), q j = 0 := by
    rw [Finset.sum_subset hsub, hsum]
    intro x hx hx'
    rw [mem_range] at hx hx'
    exact hgt x (by omega) hx
  have hqu' : ∑ j ∈ range (m + 1), (q j : ℝ) * u j = 0 := by
    rw [Finset.sum_subset hsub, hqu]
    intro x hx hx'
    rw [mem_range] at hx hx'
    rw [hgt x (by omega) hx]
    simp
  have hqm1 : (1 : ℝ) ≤ |(q m : ℝ)| := by exact_mod_cast Int.one_le_abs hmP
  have hS : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) ≤ τ + 1 := by
    calc (∑ j ∈ Ico 1 m, |(q j : ℝ)|) ≤ ∑ _j ∈ Ico 1 m, B :=
          Finset.sum_le_sum fun j hj => hB j (by rw [mem_Ico] at hj; omega)
      _ = ((m - 1 : ℕ) : ℝ) * B := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (n : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast (by omega : m - 1 ≤ n)
      _ ≤ τ + 1 := hBτ
  have hS0 : 0 ≤ ∑ j ∈ Ico 1 m, |(q j : ℝ)| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hτ' : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ := by
    have := div_le_self hS0 hqm1
    linarith
  exact lemmaB_proof n τ u q m hu hτ0 (by omega) hmP hsum' hτ' hqu'

theorem inc_decomp (n : ℕ) (e : ℕ × ℕ) (k : ℕ) (he : e.2 ≤ n) :
    inc n e k = 2 * (if e.2 < n ∧ (e.1 = k ∨ e.2 = k) then 1 else 0)
      - (if e.2 = n ∧ e.1 = k then 1 else 0) := by
  unfold inc
  split_ifs <;> omega

theorem sum_inc (D : Datum) {e : ℕ × ℕ} (he : D.IsEdge e) :
    ∑ k ∈ range D.n, inc D.n e k = 5 * (if e.2 < D.n then 1 else 0) - 1 := by
  obtain ⟨h1, h2 | ⟨h2, _, _⟩⟩ := he
  · have key : ∀ k, inc D.n e k = 2 * LC.on e k := by
      intro k
      unfold inc LC.on
      by_cases hk : e.1 = k ∨ e.2 = k <;> simp [h2, hk]
    simp only [key, ← Finset.mul_sum, LC.sum_on h1 h2, h2, if_true]
    norm_num
  · have h3 : ¬e.2 < D.n := by omega
    have h4 : e.1 < D.n := by omega
    have key : ∀ k, inc D.n e k = if e.1 = k then -1 else 0 := by
      intro k
      unfold inc
      by_cases hk : e.1 = k <;> simp [h3, hk]
    simp only [key, Finset.sum_ite_eq, mem_range, h4, h3, if_true, if_false]
    norm_num

/-- A body lies on at most n − 1 body pairs of a sequence of different edges. -/
theorem pb_le {n r : ℕ} {h : ℕ → ℕ × ℕ} (hlt : ∀ i, i < r → (h i).1 < (h i).2)
    (hinj : ∀ i j, i < r → j < r → h i = h j → i = j) {k : ℕ} (hk : k < n) :
    ∑ i ∈ range r, (if (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k) then (1 : ℤ) else 0) ≤ (n : ℤ) - 1 := by
  have h1 : ∑ i ∈ range r, (if (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k) then (1 : ℤ) else 0)
      = (((range r).filter fun i => (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k)).card : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  have h2 : ((range r).filter fun i => (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k)).card
      ≤ ((range n).erase k).card := by
    apply Finset.card_le_card_of_injOn (fun i => if (h i).1 = k then (h i).2 else (h i).1)
    · intro i hi
      rw [Finset.mem_coe, mem_filter, mem_range] at hi
      have := hlt i hi.1
      rw [Finset.mem_coe, Finset.mem_erase, mem_range]
      obtain ⟨_, hi2, hi3⟩ := hi
      beta_reduce
      split_ifs <;> omega
    · intro i hi j hj hij
      rw [Finset.mem_coe, mem_filter, mem_range] at hi hj
      apply hinj i j hi.1 hj.1
      have hi' := hlt i hi.1
      have hj' := hlt j hj.1
      obtain ⟨_, _, hi3⟩ := hi
      obtain ⟨_, _, hj3⟩ := hj
      simp only at hij
      refine Prod.ext ?_ ?_ <;> (split_ifs at hij <;> omega)
  rw [Finset.card_erase_of_mem (mem_range.mpr hk), card_range] at h2
  have h3 : (((range r).filter fun i => (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k)).card : ℤ)
      ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast h2
  omega

theorem pb_nonneg {n r : ℕ} {h : ℕ → ℕ × ℕ} (k : ℕ) :
    0 ≤ ∑ i ∈ range r, (if (h i).2 < n ∧ ((h i).1 = k ∨ (h i).2 = k) then (1 : ℤ) else 0) := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

/-- The O-edge of a body occurs at most once in a sequence of different edges. -/
theorem ob_le {n r : ℕ} {h : ℕ → ℕ × ℕ} (hinj : ∀ i j, i < r → j < r → h i = h j → i = j) (k : ℕ) :
    ∑ i ∈ range r, (if (h i).2 = n ∧ (h i).1 = k then (1 : ℤ) else 0) ≤ 1 := by
  have h1 : ∑ i ∈ range r, (if (h i).2 = n ∧ (h i).1 = k then (1 : ℤ) else 0)
      = (((range r).filter fun i => (h i).2 = n ∧ (h i).1 = k).card : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  have h2 : ((range r).filter fun i => (h i).2 = n ∧ (h i).1 = k).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_filter, mem_range] at ha hb
    exact hinj a b ha.1 hb.1 (Prod.ext (ha.2.2.trans hb.2.2.symm) (ha.2.1.trans hb.2.1.symm))
  exact_mod_cast h2

theorem ob_nonneg {n r : ℕ} {h : ℕ → ℕ × ℕ} (k : ℕ) :
    0 ≤ ∑ i ∈ range r, (if (h i).2 = n ∧ (h i).1 = k then (1 : ℤ) else 0) := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

section cycle2

variable {D : Datum} {P : ℝ} {r : ℕ} {f g : ℕ → ℕ × ℕ}

theorem cycQ_decomp (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g)
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
theorem cycQ_abs (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g)
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
    rw [cycQ_decomp hc k, abs_le]
    constructor <;> linarith
  exact_mod_cast h9

/-- The parity step: the coefficient of the body of an O-edge of the cycle is odd. -/
theorem cycQ_ne_zero (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g)
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
      rw [cycQ_decomp hc, hf1, hg0]
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
      rw [cycQ_decomp hc, hg1, hf0]
      omega

/-- Step 4: N ≠ 0. -/
theorem N_ne_zero {τ : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ)
    (hu : Chamber D.n τ D.u)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    cycN D.n r f g ≠ 0 := by
  intro hN
  have hrel := relation hD hc
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
  obtain ⟨i0, hi0, hO⟩ := has_O hD hP hτ hu hc
  obtain ⟨t, ht, hqt⟩ := cycQ_ne_zero hc hi0 hO
  have hτ0 : 0 ≤ τ := by nlinarith [sq_nonneg (D.n : ℝ)]
  have hBτ : (D.n : ℝ) * (2 * (D.n : ℝ) - 1) ≤ τ + 1 := by
    have : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
    nlinarith
  exact hqt (lemmaB_apply hu hτ0 (cycQ D.n r f g) (2 * (D.n : ℝ) - 1) (fun k hk => cycQ_abs hc hk)
    hBτ hqsum hrel t ht)

end cycle2

end D4

/-- T4. -/
theorem cycle_relation_proof (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 ∧
      cycN D.n r f g ≠ 0 :=
  ⟨D4.relation hD hc, D4.N_ne_zero hD hP hτ hu hc⟩
