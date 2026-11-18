import DirectRoute.Degree

/-!
Theorem D4, the existence of a simple cycle (T3, second half), and the bound of Theorem D5′ (T5).

The cycle: start at an edge of E* and walk, leaving every node by an edge other than the one of arrival;
Step 1 makes this possible. The walk visits nodes of ζ at even times and nodes of ω at odd times. The
first time a vertex of the bipartite graph repeats closes a simple cycle.
-/

open Finset

namespace D4

/-- The walk: after an even number of steps the next edge has the same ω-node, after an odd number the
same ζ-node. -/
def walk (sw sz : ℕ × ℕ → ℕ × ℕ) (e0 : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => e0
  | k + 1 => if k % 2 = 0 then sw (walk sw sz e0 k) else sz (walk sw sz e0 k)

/-- A bipartite multigraph on finitely many vertices in which every vertex that meets an edge meets two
has a simple cycle. -/
theorem cycle_of_degree {E : Set (ℕ × ℕ)} {NZ NW : ℕ × ℕ → Finset ℕ} {N : ℕ} (hne : E.Nonempty)
    (hsubZ : ∀ e, NZ e ⊆ range N) (hsubW : ∀ e, NW e ⊆ range N)
    (hdegW : ∀ e, e ∈ E → ∃ e', e' ∈ E ∧ e' ≠ e ∧ NW e' = NW e)
    (hdegZ : ∀ e, e ∈ E → ∃ e', e' ∈ E ∧ e' ≠ e ∧ NZ e' = NZ e) :
    ∃ r f g, IsCycle E NZ NW r f g := by
  classical
  choose! sw hsw using hdegW
  choose! sz hsz using hdegZ
  obtain ⟨e0, he0⟩ := hne
  have hstep : ∀ k, walk sw sz e0 (k + 1)
      = if k % 2 = 0 then sw (walk sw sz e0 k) else sz (walk sw sz e0 k) := fun k => rfl
  have hzero : walk sw sz e0 0 ∈ E := he0
  generalize walk sw sz e0 = Eg at hstep hzero
  have hEg : ∀ k, Eg k ∈ E := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      rw [hstep]
      split_ifs
      · exact (hsw _ ih).1
      · exact (hsz _ ih).1
  have adjE : ∀ k, k % 2 = 0 → NW (Eg (k + 1)) = NW (Eg k) ∧ Eg (k + 1) ≠ Eg k := by
    intro k hk
    rw [hstep, if_pos hk]
    exact ⟨(hsw _ (hEg k)).2.2, (hsw _ (hEg k)).2.1⟩
  have adjO : ∀ k, k % 2 = 1 → NZ (Eg (k + 1)) = NZ (Eg k) ∧ Eg (k + 1) ≠ Eg k := by
    intro k hk
    rw [hstep, if_neg (by omega)]
    exact ⟨(hsz _ (hEg k)).2.2, (hsz _ (hEg k)).2.1⟩
  -- the vertex before the edge `Eg k`
  have hVdef : ∀ k, (if k % 2 = 0 then NZ (Eg k) else NW (Eg k))
      = (if k % 2 = 0 then NZ (Eg k) else NW (Eg k)) := fun k => rfl
  generalize hV : (fun k => if k % 2 = 0 then NZ (Eg k) else NW (Eg k)) = V
  have Veven : ∀ k, k % 2 = 0 → V k = NZ (Eg k) := by
    intro k hk
    rw [← hV]
    simp [hk]
  have Vodd : ∀ k, k % 2 = 1 → V k = NW (Eg k) := by
    intro k hk
    rw [← hV]
    simp [hk]
  have VsuccE : ∀ k, k % 2 = 0 → V (k + 1) = NW (Eg k) := by
    intro k hk
    rw [Vodd (k + 1) (by omega), (adjE k hk).1]
  have VsuccO : ∀ k, k % 2 = 1 → V (k + 1) = NZ (Eg k) := by
    intro k hk
    rw [Veven (k + 1) (by omega), (adjO k hk).1]
  have Vsub : ∀ k, V k ⊆ range N := by
    intro k
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [Veven k hk]
      exact hsubZ _
    · rw [Vodd k hk]
      exact hsubW _
  -- two times with the same vertex
  have hex : ∃ t, ∃ s, s < t ∧ V s = V t ∧ s % 2 = t % 2 := by
    have hK : ∀ k ∈ range (((range N).powerset ×ˢ range 2).card + 1),
        (V k, k % 2) ∈ (range N).powerset ×ˢ range 2 := by
      intro k _
      rw [mem_product, mem_powerset, mem_range]
      exact ⟨Vsub k, Nat.mod_lt _ (by norm_num)⟩
    obtain ⟨x, _, y, _, hxy, hKxy⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [card_range]; omega) hK
    have h1 : V x = V y := congrArg Prod.fst hKxy
    have h2 : x % 2 = y % 2 := congrArg Prod.snd hKxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, h1, h2⟩
    · exact ⟨x, y, h, h1.symm, h2.symm⟩
  obtain ⟨s0, hs0, hV0, hpar0⟩ := Nat.find_spec hex
  have hmin : ∀ t, t < Nat.find hex → ¬∃ s, s < t ∧ V s = V t ∧ s % 2 = t % 2 :=
    fun t ht => Nat.find_min hex ht
  generalize Nat.find hex = t0 at hs0 hV0 hpar0 hmin
  have Kinj : ∀ p q, p < t0 → q < t0 → V p = V q → p % 2 = q % 2 → p = q := by
    intro p q hp hq h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hmin q hq ⟨p, h, h1, h2⟩
    · exact hmin p hp ⟨q, h, h1.symm, h2.symm⟩
  have Einj : ∀ p q, p < q → q < t0 → Eg p ≠ Eg q := by
    intro p q hpq hq heq
    by_cases hpar : p % 2 = q % 2
    · have h1 : V p = V q := by
        rcases Nat.mod_two_eq_zero_or_one p with hp | hp
        · rw [Veven p hp, Veven q (by omega), heq]
        · rw [Vodd p hp, Vodd q (by omega), heq]
      have := Kinj p q (by omega) hq h1 hpar
      omega
    · have h1 : V (p + 1) = V q := by
        rcases Nat.mod_two_eq_zero_or_one p with hp | hp
        · rw [VsuccE p hp, Vodd q (by omega), heq]
        · rw [VsuccO p hp, Veven q (by omega), heq]
      rcases Nat.lt_or_ge (p + 1) q with h | h
      · have := Kinj (p + 1) q (by omega) hq h1 (by omega)
        omega
      · have hq' : q = p + 1 := by omega
        subst hq'
        rcases Nat.mod_two_eq_zero_or_one p with hp | hp
        · exact (adjE p hp).2 heq.symm
        · exact (adjO p hp).2 heq.symm
  have EinjAll : ∀ p q, p < t0 → q < t0 → Eg p = Eg q → p = q := by
    intro p q hp hq h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact Einj p q h1 hq h
    · exact Einj q p h1 hp h.symm
  obtain ⟨r, hr⟩ : ∃ r, t0 = s0 + 2 * r := ⟨(t0 - s0) / 2, by omega⟩
  have hr1 : 1 ≤ r := by omega
  rcases Nat.mod_two_eq_zero_or_one s0 with hs | hs
  · -- the window starts at a node of ζ
    refine ⟨r, fun k => Eg (s0 + 2 * k), fun k => Eg (s0 + 2 * k + 1), ?_⟩
    refine ⟨hr1, fun i _ => hEg _, fun i _ => hEg _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i _
      exact ((adjE (s0 + 2 * i) (by omega)).1).symm
    · intro i hi
      show NZ (Eg (s0 + 2 * i + 1)) = NZ (Eg (s0 + 2 * ((i + 1) % r)))
      by_cases h1 : i + 1 < r
      · rw [Nat.mod_eq_of_lt h1]
        have := (adjO (s0 + 2 * i + 1) (by omega)).1
        rw [show s0 + 2 * (i + 1) = s0 + 2 * i + 1 + 1 by ring]
        exact this.symm
      · have hir : i + 1 = r := by omega
        rw [hir, Nat.mod_self]
        have h2 := VsuccO (s0 + 2 * i + 1) (by omega)
        have h3 : s0 + 2 * i + 1 + 1 = t0 := by omega
        rw [h3, ← hV0, Veven s0 hs] at h2
        simpa using h2.symm
    · intro i j hi hj h
      have := EinjAll (s0 + 2 * i) (s0 + 2 * j) (by omega) (by omega) h
      omega
    · intro i j hi hj h
      have := EinjAll (s0 + 2 * i + 1) (s0 + 2 * j + 1) (by omega) (by omega) h
      omega
    · intro i j hi hj h
      have := EinjAll (s0 + 2 * i) (s0 + 2 * j + 1) (by omega) (by omega) h
      omega
    · intro i j hi hj h
      have e1 := VsuccE (s0 + 2 * i) (by omega)
      have e2 := VsuccE (s0 + 2 * j) (by omega)
      have := Kinj (s0 + 2 * i + 1) (s0 + 2 * j + 1) (by omega) (by omega) (by rw [e1, e2]; exact h)
        (by omega)
      omega
    · intro i j hi hj h
      have e1 := Veven (s0 + 2 * i) (by omega)
      have e2 := Veven (s0 + 2 * j) (by omega)
      have := Kinj (s0 + 2 * i) (s0 + 2 * j) (by omega) (by omega) (by rw [e1, e2]; exact h) (by omega)
      omega
  · -- the window starts at a node of ω
    have hlast : ∀ i, i + 1 = r → NW (Eg (s0 + 2 * i + 1)) = NW (Eg s0) := by
      intro i hir
      have h2 := VsuccE (s0 + 2 * i + 1) (by omega)
      have h3 : s0 + 2 * i + 1 + 1 = t0 := by omega
      rw [h3, ← hV0, Vodd s0 hs] at h2
      exact h2.symm
    refine ⟨r, fun k => Eg (s0 + 2 * k + 1),
      fun k => if k + 1 < r then Eg (s0 + 2 * k + 2) else Eg s0, ?_⟩
    refine ⟨hr1, fun i _ => hEg _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i _
      show (if i + 1 < r then Eg (s0 + 2 * i + 2) else Eg s0) ∈ E
      split_ifs
      · exact hEg _
      · exact hEg _
    · intro i hi
      show NW (Eg (s0 + 2 * i + 1)) = NW (if i + 1 < r then Eg (s0 + 2 * i + 2) else Eg s0)
      split_ifs with h1
      · exact ((adjE (s0 + 2 * i + 1) (by omega)).1).symm
      · exact hlast i (by omega)
    · intro i hi
      show NZ (if i + 1 < r then Eg (s0 + 2 * i + 2) else Eg s0)
        = NZ (Eg (s0 + 2 * ((i + 1) % r) + 1))
      split_ifs with h1
      · rw [Nat.mod_eq_of_lt h1]
        have := (adjO (s0 + 2 * i + 2) (by omega)).1
        rw [show s0 + 2 * (i + 1) + 1 = s0 + 2 * i + 2 + 1 by ring]
        exact this.symm
      · have hir : i + 1 = r := by omega
        rw [hir, Nat.mod_self]
        have := (adjO s0 hs).1
        simpa using this.symm
    · intro i j hi hj h
      have := EinjAll (s0 + 2 * i + 1) (s0 + 2 * j + 1) (by omega) (by omega) h
      omega
    · intro i j hi hj h
      have h' : (if i + 1 < r then Eg (s0 + 2 * i + 2) else Eg s0)
          = (if j + 1 < r then Eg (s0 + 2 * j + 2) else Eg s0) := h
      split_ifs at h' with h1 h2 h2
      · have := EinjAll (s0 + 2 * i + 2) (s0 + 2 * j + 2) (by omega) (by omega) h'
        omega
      · have := EinjAll (s0 + 2 * i + 2) s0 (by omega) (by omega) h'
        omega
      · have := EinjAll s0 (s0 + 2 * j + 2) (by omega) (by omega) h'
        omega
      · omega
    · intro i j hi hj h
      have h' : Eg (s0 + 2 * i + 1) = (if j + 1 < r then Eg (s0 + 2 * j + 2) else Eg s0) := h
      split_ifs at h' with h1
      · have := EinjAll (s0 + 2 * i + 1) (s0 + 2 * j + 2) (by omega) (by omega) h'
        omega
      · have := EinjAll (s0 + 2 * i + 1) s0 (by omega) (by omega) h'
        omega
    · intro i j hi hj h
      -- the ω-node of `f i` is the vertex at time s0 + 2 i + 2, or at time s0 for the last i
      have hv : ∀ i, i < r → ∃ p, p < t0 ∧ p % 2 = 1 ∧ V p = NW (Eg (s0 + 2 * i + 1)) ∧
          p = (if i + 1 < r then s0 + 2 * i + 2 else s0) := by
        intro i hi
        by_cases h1 : i + 1 < r
        · exact ⟨s0 + 2 * i + 2, by omega, by omega, VsuccE (s0 + 2 * i + 1) (by omega), by simp [h1]⟩
        · refine ⟨s0, by omega, hs, ?_, by simp [h1]⟩
          rw [Vodd s0 hs]
          exact (hlast i (by omega)).symm
      obtain ⟨p, hp, hp2, hVp, hpe⟩ := hv i hi
      obtain ⟨q, hq, hq2, hVq, hqe⟩ := hv j hj
      have hpq := Kinj p q hp hq (by rw [hVp, hVq]; exact h) (by omega)
      rw [hpe, hqe] at hpq
      split_ifs at hpq <;> omega
    · intro i j hi hj h
      have e1 := Veven (s0 + 2 * i + 1) (by omega)
      have e2 := Veven (s0 + 2 * j + 1) (by omega)
      have := Kinj (s0 + 2 * i + 1) (s0 + 2 * j + 1) (by omega) (by omega) (by rw [e1, e2]; exact h)
        (by omega)
      omega

end D4

/-- T3, second half. -/
theorem exists_cycle_proof (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) :
    ∃ r f g, IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g := by
  apply D4.cycle_of_degree (N := D.n + 1)
  · obtain ⟨e, he1, he2⟩ := hP.2
    exact ⟨e, he1, he2⟩
  · intro e
    unfold node
    exact Finset.filter_subset _ _
  · intro e
    unfold node
    exact Finset.filter_subset _ _
  · intro e he
    exact (degree_two_proof D P hD hP e he).1
  · intro e he
    exact (degree_two_proof D P hD hP e he).2

/-- T5. -/
theorem collision_bound_proof (D : Datum) (τ : ℝ) (hD : D.IsWeightDatum)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (t l : ℕ) (htl : t < l) (hl : l < D.n) :
    D.z t l + D.w t l
      ≤ 2 * (2 * (D.n : ℝ) - 1) * (∑ j ∈ range D.n, |D.u j|) / 3 + 2 * D.u t + 2 * D.u l := by
  classical
  have h2 := hD.two
  -- Ψ* exists
  obtain ⟨P, hP⟩ : ∃ P, D.IsPsiStar P := by
    have hne : (((range (D.n + 1)) ×ˢ (range (D.n + 1))).filter fun e => D.IsEdge e).Nonempty := by
      refine ⟨(0, 1), ?_⟩
      rw [mem_filter, mem_product, mem_range, mem_range]
      exact ⟨⟨by omega, by show 1 < D.n + 1; omega⟩, ⟨by norm_num, Or.inl (by show 1 < D.n; omega)⟩⟩
    obtain ⟨e, he, hmax⟩ := Finset.exists_max_image _ D.psiE hne
    rw [mem_filter] at he
    refine ⟨D.psiE e, fun e' he' => hmax e' ?_, ⟨e, he.2, rfl⟩⟩
    rw [mem_filter, mem_product, mem_range, mem_range]
    have := D4.edge_le D he'
    exact ⟨⟨by omega, by omega⟩, he'⟩
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
  have hP3 : P ≤ (2 * (D.n : ℝ) - 1) * (∑ k ∈ range D.n, |D.u k|) / 3 := by
    have e1 : (cycN D.n r f g : ℝ) * P = -∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k := by
      linarith
    have e2 : |(cycN D.n r f g : ℝ)| * |P| = |∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k| := by
      rw [← abs_mul, e1, abs_neg]
    have e3 := mul_le_mul_of_nonneg_right hN3 (abs_nonneg P)
    have e4 := le_abs_self P
    linarith
  have hpsi := hP.1 (t, l) ⟨htl, Or.inl hl⟩
  simp only [Datum.psiE, Nat.ne_of_lt hl, ite_false] at hpsi
  unfold psiPair at hpsi
  linarith
