"""Writes lean/direct-route/DirectRoute/Degree.lean: Step 1 of Theorem D4 for the two colours, from one
template in which the names of the colour of the cut and of the other colour are placeholders.

Usage: python3 scripts/allN/lean_gen_degree.py   (from the repository root)
"""
import io, re
head = r'''import DirectRoute.Relation

/-!
Theorem D4, Step 1 (T3, first half): every node of an edge of E* is the node of a second edge of E*.
The proof of the brief: a child of the node that contains one end of the edge and not the vertex O is a
set of bodies; in its cut identity the largest value is Ψ* plus the height of the node, and a term
attains it only if its edge lies in E* and has this node. The two colours have the same proof; the two
versions below differ by the exchange of ζ and ω.
-/

open Finset

namespace D4

/-- A pair in the order of an edge: the smaller index first. -/
def canon (e : ℕ × ℕ) : ℕ × ℕ := if e.1 < e.2 then e else (e.2, e.1)

/-- (T4) of the brief: two points of a node at the height of the node have this node. -/
theorem node_eq_of {N : ℕ} {d : ℕ → ℕ → WithTop ℝ} (h : IsUltra N d) {a b t l : ℕ} (ha : a < N)
    (ht : t ∈ node N d (a, b)) (hl : l ∈ node N d (a, b)) (htl : t ≠ l) (hd : d t l = d a b) :
    node N d (t, l) = node N d (a, b) := by
  have htN := (mem_node.mp ht).1
  ext p
  constructor
  · intro hp
    obtain ⟨hpN, hp⟩ := mem_node.mp hp
    simp only at hp
    rcases hp with rfl | hp
    · exact ht
    · rw [hd] at hp
      rw [mem_node]
      refine ⟨hpN, ?_⟩
      simp only
      by_cases hpa : p = a
      · exact Or.inl hpa
      · right
        by_cases hta : t = a
        · have e3 : d a p = d t p := by rw [hta]
          rw [e3]
          exact hp
        · have h1 : d a b ≤ d a t := by
            rcases (mem_node.mp ht).2 with h1 | h1
            · exact absurd h1 hta
            · exact h1
          by_cases hpt : p = t
          · rw [hpt]
            exact h1
          · have tri := h.2 a t p ha htN hpN (Ne.symm hta) (Ne.symm hpt) (Ne.symm hpa)
            exact le_trans (le_min h1 hp) tri
  · intro hp
    rw [mem_node]
    refine ⟨(mem_node.mp hp).1, ?_⟩
    simp only
    by_cases hpt : p = t
    · exact Or.inl hpt
    · right
      rw [hd]
      exact node_pair h ha ht hp (Ne.symm hpt)

theorem psi_symm {D : Datum} (hD : D.IsWeightDatum) {a b : ℕ} (ha : a < D.n) (hb : b < D.n) :
    psiPair D.u D.z D.w a b = psiPair D.u D.z D.w b a := by
  have hz : D.z a b = D.z b a := by
    have := hD.ultra_z.1 a b (by omega) (by omega)
    rw [dz_body D ha hb, dz_body D hb ha] at this
    exact_mod_cast this
  have hw : D.w a b = D.w b a := by
    have := hD.ultra_w.1 a b (by omega) (by omega)
    rw [dw_body D ha hb, dw_body D hb ha] at this
    exact_mod_cast this
  unfold psiPair
  rw [hz, hw]
  ring
'''
template = r'''
/-- The cut of colour «CZ» at a child of a node: two different edges of E* with this node. -/
theorem degree_aux_cut«CZ» {D : Datum} {P : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    {c o : ℕ} {h : ℝ} (hc : c < D.n) (ho : o < D.n ∨ (o = D.n ∧ D.«NP» c ≠ ⊤)) (hco : c ≠ o)
    (hd : D.«OD» c o = (h : WithTop ℝ)) (hO : ¬((h : WithTop ℝ) < D.«OD» c D.n))
    (hval : D.«PHI» c o = P + h) :
    ∃ e₁ e₂ : ℕ × ℕ, e₁ ≠ e₂ ∧ e₁ ∈ D.Estar P ∧ e₂ ∈ D.Estar P ∧
      node (D.n + 1) D.«OD» e₁ = node (D.n + 1) D.«OD» (c, o) ∧
      node (D.n + 1) D.«OD» e₂ = node (D.n + 1) D.«OD» (c, o) := by
  classical
  have hSdef : ∀ p, p ∈ (range D.n).filter (fun p => p = c ∨ (h : WithTop ℝ) < D.«OD» c p) ↔
      p < D.n ∧ (p = c ∨ (h : WithTop ℝ) < D.«OD» c p) := by
    intro p
    rw [mem_filter, mem_range]
  generalize (range D.n).filter (fun p => p = c ∨ (h : WithTop ℝ) < D.«OD» c p) = S at hSdef
  have hSsub : S ⊆ range D.n := by
    intro p hp
    rw [mem_range]
    exact ((hSdef p).mp hp).1
  have hcS : c ∈ S := (hSdef c).mpr ⟨hc, Or.inl rfl⟩
  have star : ∀ t l, t ∈ S → l ≤ D.n → l ≠ c → ¬((h : WithTop ℝ) < D.«OD» c l) → l ≠ t →
      D.«OD» t l ≤ (h : WithTop ℝ) := by
    intro t l htS hl hlc hnl hlt
    obtain ⟨htn, ht⟩ := (hSdef t).mp htS
    by_cases htc : t = c
    · subst htc
      exact not_lt.mp hnl
    · have ht' : (h : WithTop ℝ) < D.«OD» c t := by
        rcases ht with ht | ht
        · exact absurd ht htc
        · exact ht
      by_contra hgt
      rw [not_le] at hgt
      have tri := hD.«OU».2 c t l (by omega) (by omega) (by omega) (Ne.symm htc) (Ne.symm hlt)
        (Ne.symm hlc)
      exact hnl (lt_of_lt_of_le (lt_min ht' hgt) tri)
  have inNode : ∀ t l, t ∈ S → l ≤ D.n → l ≠ c → l ≠ t → D.«OD» t l = (h : WithTop ℝ) →
      t ∈ node (D.n + 1) D.«OD» (c, o) ∧ l ∈ node (D.n + 1) D.«OD» (c, o) := by
    intro t l htS hl hlc hlt hdtl
    obtain ⟨htn, ht⟩ := (hSdef t).mp htS
    constructor
    · rw [mem_node]
      refine ⟨by omega, ?_⟩
      rcases ht with ht | ht
      · exact Or.inl ht
      · right
        show D.«OD» c o ≤ D.«OD» c t
        rw [hd]
        exact le_of_lt ht
    · rw [mem_node]
      refine ⟨by omega, Or.inr ?_⟩
      show D.«OD» c o ≤ D.«OD» c l
      rw [hd]
      by_cases htc : t = c
      · subst htc
        rw [hdtl]
      · have ht' : (h : WithTop ℝ) < D.«OD» c t := by
          rcases ht with ht | ht
          · exact absurd ht htc
          · exact ht
        have tri := hD.«OU».2 c t l (by omega) (by omega) (by omega) (Ne.symm htc) (Ne.symm hlt)
          (Ne.symm hlc)
        rw [hdtl] at tri
        exact le_trans (le_min (le_of_lt ht') le_rfl) tri
  have key : ∀ e : ℕ × ℕ, e ∈ D.«TERMS» S → D.«PHI» e.1 e.2 ≤ P + h ∧
      (D.«PHI» e.1 e.2 = P + h → canon e ∈ D.Estar P ∧ D.«OD» e.1 e.2 = (h : WithTop ℝ) ∧
        e.2 ≤ D.n ∧ e.2 ≠ c ∧ e.2 ≠ e.1) := by
    rintro ⟨t, l⟩ hmem
    have htS : t ∈ S := hmem.1
    have hl : (l < D.n ∧ l ∉ S) ∨ (l = D.n ∧ D.«NP» t ≠ ⊤) := hmem.2
    show D.«PHI» t l ≤ P + h ∧ (D.«PHI» t l = P + h → canon (t, l) ∈ D.Estar P ∧
      D.«OD» t l = (h : WithTop ℝ) ∧ l ≤ D.n ∧ l ≠ c ∧ l ≠ t)
    obtain ⟨htn, ht⟩ := (hSdef t).mp htS
    rcases hl with ⟨hln, hlS⟩ | ⟨hln, hown⟩
    · have hl' : l ≠ c ∧ ¬((h : WithTop ℝ) < D.«OD» c l) := by
        constructor
        · intro hh
          exact hlS ((hSdef l).mpr ⟨hln, Or.inl hh⟩)
        · intro hh
          exact hlS ((hSdef l).mpr ⟨hln, Or.inr hh⟩)
      have hlt : l ≠ t := fun hh => hlS (hh ▸ htS)
      have hle := star t l htS hln.le hl'.1 hl'.2 hlt
      rw [«OB» D htn hln] at hle
      have hle' : D.«OH» t l ≤ h := by exact_mod_cast hle
      have hpsi : psiPair D.u D.z D.w t l ≤ P := by
        rcases lt_or_gt_of_ne hlt with h1 | h1
        · have := hP.1 (l, t) ⟨h1, Or.inl htn⟩
          simp only [Datum.psiE, Nat.ne_of_lt htn, ite_false] at this
          rw [psi_symm hD htn hln]
          exact this
        · have := hP.1 (t, l) ⟨h1, Or.inl hln⟩
          simp only [Datum.psiE, Nat.ne_of_lt hln, ite_false] at this
          exact this
      have hphi : D.«PHI» t l = psiPair D.u D.z D.w t l + D.«OH» t l := by
        simp [Datum.«PHI», Nat.ne_of_lt hln]
      refine ⟨by rw [hphi]; linarith, fun htight => ?_⟩
      rw [hphi] at htight
      have e1 : psiPair D.u D.z D.w t l = P := by linarith
      have e2 : D.«OH» t l = h := by linarith
      refine ⟨?_, by rw [«OB» D htn hln, e2], hln.le, hl'.1, hlt⟩
      unfold canon
      rcases lt_or_gt_of_ne hlt with h1 | h1
      · have h1' : ¬t < l := by omega
        simp only [h1', ite_false]
        refine ⟨⟨h1, Or.inl htn⟩, ?_⟩
        simp only [Datum.psiE, Nat.ne_of_lt htn, ite_false]
        rw [← psi_symm hD htn hln]
        exact e1
      · simp only [h1, ite_true]
        refine ⟨⟨h1, Or.inl hln⟩, ?_⟩
        simp only [Datum.psiE, Nat.ne_of_lt hln, ite_false]
        exact e1
    · subst hln
      have htne : t ≠ D.n := Nat.ne_of_lt htn
      have hle := star t D.n htS le_rfl (Nat.ne_of_gt hc) hO (Ne.symm htne)
      have hdt : D.«OD» t D.n = D.«OP» t := by simp [Datum.«OD», htne]
      rw [hdt] at hle
      have hoth : D.«OP» t ≠ ⊤ := by
        intro hh
        rw [hh] at hle
        exact WithTop.coe_ne_top (top_le_iff.mp hle)
      have hη : (D.«OP» t).untopD 0 ≤ h := by
        have h3 : (((D.«OP» t).untopD 0 : ℝ) : WithTop ℝ) ≤ (h : WithTop ℝ) := by
          rw [coe_untopD hoth]
          exact hle
        exact_mod_cast h3
      have hpsi := hP.1 (t, D.n) ⟨htn, Or.inr ⟨rfl, «LIVE»⟩⟩
      simp only [Datum.psiE, ite_true, Datum.psiO] at hpsi
      have hphi : D.«PHI» t D.n = -D.u t - (D.«NP» t).untopD 0 := by simp [Datum.«PHI»]
      refine ⟨by rw [hphi]; linarith, fun htight => ?_⟩
      rw [hphi] at htight
      have e2 : (D.«OP» t).untopD 0 = h := by linarith
      refine ⟨?_, by rw [hdt, ← coe_untopD hoth, e2], le_rfl, Nat.ne_of_gt hc, Ne.symm htne⟩
      unfold canon
      simp only [htn, ite_true]
      refine ⟨⟨htn, Or.inr ⟨rfl, «LIVE»⟩⟩, ?_⟩
      simp only [Datum.psiE, ite_true, Datum.psiO]
      linarith
  have hco_term : (c, o) ∈ D.«TERMS» S := by
    refine ⟨hcS, ?_⟩
    rcases ho with h1 | ⟨h1, h2⟩
    · left
      refine ⟨h1, fun hoS => ?_⟩
      obtain ⟨_, h3⟩ := (hSdef o).mp hoS
      rcases h3 with h3 | h3
      · exact hco h3.symm
      · rw [hd] at h3
        exact lt_irrefl _ h3
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨e₁, e₂, m₁, m₂, hne, heq, hmax⟩ := hD.«CUT» S hSsub ⟨c, hcS⟩
  have hv1 : D.«PHI» e₁.1 e₁.2 = P + h := by
    apply le_antisymm (key e₁ m₁).1
    have := hmax (c, o) hco_term
    simp only at this
    linarith
  have hv2 : D.«PHI» e₂.1 e₂.2 = P + h := by
    rw [← heq]
    exact hv1
  obtain ⟨c1, d1, l1, lc1, lt1⟩ := (key e₁ m₁).2 hv1
  obtain ⟨c2, d2, l2, lc2, lt2⟩ := (key e₂ m₂).2 hv2
  have n1 := inNode e₁.1 e₁.2 m₁.1 l1 lc1 lt1 d1
  have n2 := inNode e₂.1 e₂.2 m₂.1 l2 lc2 lt2 d2
  have t1 := ((hSdef e₁.1).mp m₁.1).1
  have t2 := ((hSdef e₂.1).mp m₂.1).1
  refine ⟨canon e₁, canon e₂, ?_, c1, c2, ?_, ?_⟩
  · intro hcan
    apply hne
    have o1 : e₁.2 ∉ S := by
      rcases m₁.2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · exact h3
      · intro hh
        have := ((hSdef _).mp hh).1
        omega
    have o2 : e₂.2 ∉ S := by
      rcases m₂.2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · exact h3
      · intro hh
        have := ((hSdef _).mp hh).1
        omega
    unfold canon at hcan
    split_ifs at hcan with ha hb hb
    · exact hcan
    · have h3 : e₁.1 = e₂.2 := congrArg Prod.fst hcan
      exact absurd (h3 ▸ m₁.1) o2
    · have h3 : e₁.2 = e₂.1 := congrArg Prod.fst hcan
      exact absurd (h3 ▸ m₂.1) o1
    · have h3 : e₁.2 = e₂.2 := congrArg Prod.fst hcan
      have h4 : e₁.1 = e₂.1 := congrArg Prod.snd hcan
      exact Prod.ext h4 h3
  · unfold canon
    split_ifs with ha
    · exact node_eq_of hD.«OU» (by omega) n1.1 n1.2 (Ne.symm lt1) (by rw [d1, hd])
    · exact node_eq_of hD.«OU» (by omega) n1.2 n1.1 lt1
        (by rw [hD.«OU».1 e₁.2 e₁.1 (by omega) (by omega), d1, hd])
  · unfold canon
    split_ifs with ha
    · exact node_eq_of hD.«OU» (by omega) n2.1 n2.2 (Ne.symm lt2) (by rw [d2, hd])
    · exact node_eq_of hD.«OU» (by omega) n2.2 n2.1 lt2
        (by rw [hD.«OU».1 e₂.2 e₂.1 (by omega) (by omega), d2, hd])

/-- Step 1 for one colour: the node of an edge of E* is the node of a second edge of E*. -/
theorem degree_half_cut«CZ» {D : Datum} {P : ℝ} (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    {e : ℕ × ℕ} (he : e ∈ D.Estar P) :
    ∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.«OD» e' = node (D.n + 1) D.«OD» e := by
  obtain ⟨hedge, hpsi⟩ := he
  have hle := edge_le D hedge
  have hd := «OE» D hedge
  have hx : e.1 < D.n := by omega
  have main : ∃ c o : ℕ, c < D.n ∧ (o < D.n ∨ (o = D.n ∧ D.«NP» c ≠ ⊤)) ∧ c ≠ o ∧
      D.«OD» c o = ((«OHH» D e : ℝ) : WithTop ℝ) ∧ ¬(((«OHH» D e : ℝ) : WithTop ℝ) < D.«OD» c D.n) ∧
      D.«PHI» c o = P + «OHH» D e ∧ node (D.n + 1) D.«OD» e = node (D.n + 1) D.«OD» (c, o) := by
    by_cases hOx : ((«OHH» D e : ℝ) : WithTop ℝ) < D.«OD» e.1 D.n
    · have hy : e.2 < D.n := by
        rcases hedge.2 with h2 | ⟨h2, _, _⟩
        · exact h2
        · rw [h2] at hd
          rw [hd] at hOx
          exact absurd hOx (lt_irrefl _)
      have hyn : e.2 ≠ D.n := Nat.ne_of_lt hy
      have hsym : D.«OD» e.2 e.1 = D.«OD» e.1 e.2 := hD.«OU».1 e.2 e.1 (by omega) (by omega)
      refine ⟨e.2, e.1, hy, Or.inl hx, Nat.ne_of_gt hedge.1, by rw [hsym, hd], ?_, ?_, ?_⟩
      · intro hOy
        have tri := hD.«OU».2 e.1 D.n e.2 (by omega) (by omega) (by omega) (Nat.ne_of_lt hx)
          (Ne.symm hyn) (Nat.ne_of_lt hedge.1)
        rw [hD.«OU».1 D.n e.2 (by omega) (by omega), hd] at tri
        exact absurd (lt_of_lt_of_le (lt_min hOx hOy) tri) (lt_irrefl _)
      · have e1 : psiPair D.u D.z D.w e.1 e.2 = P := by
          simpa [Datum.psiE, hyn] using hpsi
        have e2 : D.«OH» e.2 e.1 = «OHH» D e := by
          have h3 := hsym
          rw [«OB» D hy hx, «OB» D hx hy] at h3
          have h4 : D.«OH» e.2 e.1 = D.«OH» e.1 e.2 := by exact_mod_cast h3
          rw [h4]
          simp [«OHH», hyn]
        have h5 : D.«PHI» e.2 e.1 = psiPair D.u D.z D.w e.2 e.1 + D.«OH» e.2 e.1 := by
          simp [Datum.«PHI», Nat.ne_of_lt hx]
        rw [h5, psi_symm hD hy hx, e1, e2]
      · exact node_eq_of hD.«OU» (by omega) (mem_node.mpr ⟨by omega, Or.inr le_rfl⟩)
          (mem_node.mpr ⟨by omega, Or.inl rfl⟩) (Nat.ne_of_lt hedge.1) hsym.symm
    · refine ⟨e.1, e.2, hx, ?_, Nat.ne_of_lt hedge.1, hd, hOx, ?_, rfl⟩
      · rcases hedge.2 with h2 | ⟨h2, «LIVE»⟩
        · exact Or.inl h2
        · exact Or.inr ⟨h2, hown⟩
      · rcases hedge.2 with h2 | ⟨h2, _, _⟩
        · have hyn := Nat.ne_of_lt h2
          have e1 : psiPair D.u D.z D.w e.1 e.2 = P := by
            simpa [Datum.psiE, hyn] using hpsi
          simp [Datum.«PHI», «OHH», hyn, e1]
        · simp only [Datum.psiE, h2, ite_true, Datum.psiO] at hpsi
          simp only [Datum.«PHI», «OHH», h2, ite_true]
          linarith
  obtain ⟨c, o, hc, ho, hco, hd', hO, hval, hnode⟩ := main
  obtain ⟨e₁, e₂, hne, m₁, m₂, n₁, n₂⟩ := degree_aux_cut«CZ» hD hP hc ho hco hd' hO hval
  by_cases h1 : e₁ = e
  · exact ⟨e₂, m₂, fun h2 => hne (h1.trans h2.symm), by rw [n₂, hnode]⟩
  · exact ⟨e₁, m₁, h1, by rw [n₁, hnode]⟩
'''
tail = r'''
end D4

/-- T3, first half. -/
theorem degree_two_proof (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (e : ℕ × ℕ) (he : e ∈ D.Estar P) :
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dw e' = node (D.n + 1) D.dw e) ∧
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dz e' = node (D.n + 1) D.dz e) :=
  ⟨D4.degree_half_cutZ hD hP he, D4.degree_half_cutW hD hP he⟩
'''
Z = {'CZ':'Z','NP':'xi','OP':'eta','OD':'dw','OU':'ultra_w','OB':'dw_body','OE':'dw_eq','OH':'w','OHH':'wh',
     'PHI':'phiZ','TERMS':'termsZ','CUT':'cut_z','LIVE':'hown, hoth'}
W = {'CZ':'W','NP':'eta','OP':'xi','OD':'dz','OU':'ultra_z','OB':'dz_body','OE':'dz_eq','OH':'z','OHH':'zh',
     'PHI':'phiW','TERMS':'termsW','CUT':'cut_w','LIVE':'hoth, hown'}
def inst(t, m):
    return re.sub(r'«(\w+)»', lambda mm: m[mm.group(1)], t)
out = head + inst(template, Z) + inst(template, W) + tail
io.open('lean/direct-route/DirectRoute/Degree.lean','w',encoding='utf-8').write(out)
print(len(out.splitlines()))
