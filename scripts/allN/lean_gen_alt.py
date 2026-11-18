"""Writes lean/direct-route/DirectRoute/DefsB.lean (the definition of ChallengeB.lean, copied) and
lean/direct-route/DirectRoute/Alt.lean (the proofs of the statements of ChallengeB.lean).

The proofs of Theorem 6.2 (b), (c) for closed alternating sequences are the proofs of
DirectRoute/Relation.lean for simple cycles, with two changes: the hypothesis is `IsAltSeq` on the
heights in place of `IsCycle` on the nodes, and the two lemmas that pass from equal nodes to equal
heights are replaced by direct ones. This script copies the two sections of Relation.lean that depend
on the cycle and makes these changes, so that the two proofs cannot drift apart.

Usage: python3 scripts/allN/lean_gen_alt.py   (from the repository root)
"""
import io
import re

P = 'lean/direct-route/'
ch = io.open(P + 'ChallengeB.lean', encoding='utf-8').read()

# --- DefsB.lean: the structure IsAltSeq, copied
m = re.search(r'/-- A closed alternating sequence.*?ne_fg : [^\n]*\n', ch, re.S)
assert m, 'IsAltSeq not found in ChallengeB.lean'
defsB = '''import DirectRoute.Defs

/-!
The definition of `ChallengeB.lean`, copied without change for the solution.
-/

open Finset

noncomputable section

''' + m.group(0) + '''
end
'''
io.open(P + 'DirectRoute/DefsB.lean', 'w', encoding='utf-8').write(defsB)

# --- Alt.lean
rel = io.open(P + 'DirectRoute/Relation.lean', encoding='utf-8').read()


def block(start, end):
    i = rel.index(start)
    j = rel.index(end, i) + len(end)
    return rel[i:j]


OLD = 'IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g'
NEW = 'IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g'

b1 = block('section cycle\n', 'end cycle\n')
b2 = block('section cycle2\n', 'end cycle2\n')

# the two adjacency lemmas of Relation.lean are replaced
i = b1.index('theorem adj_wh')
j = b1.index('/-- Step 2: the relation')
ADJ = '''theorem adj_whA (_hD : D.IsWeightDatum)
    (hc : ''' + NEW + ''') {i : ℕ} (hi : i < r) :
    wh D (f i) = wh D (g i) := by
  have ef := (hc.mem_f i hi).1
  have eg := (hc.mem_g i hi).1
  have h : D.dw (f i).1 (f i).2 = D.dw (g i).1 (g i).2 := hc.adj_w i hi
  rw [dw_eq D ef, dw_eq D eg] at h
  exact_mod_cast h

theorem adj_zhA (_hD : D.IsWeightDatum)
    (hc : ''' + NEW + ''') {i : ℕ} (hi : i < r) :
    zh D (g i) = zh D (f ((i + 1) % r)) := by
  have hi' : (i + 1) % r < r := Nat.mod_lt _ (by omega)
  have ef := (hc.mem_f _ hi').1
  have eg := (hc.mem_g i hi).1
  have h : D.dz (g i).1 (g i).2 = D.dz (f ((i + 1) % r)).1 (f ((i + 1) % r)).2 := hc.adj_z i hi
  rw [dz_eq D eg, dz_eq D ef] at h
  exact_mod_cast h

'''
b1 = b1[:i] + ADJ + b1[j:]

RENAMES = [
    ('theorem relation ', 'theorem relationA '),
    ('relation hD hc', 'relationA hD hc'),
    ('theorem has_O ', 'theorem has_OA '),
    ('has_O hD hP hτ hu hc', 'has_OA hD hP hτ hu hc'),
    ('theorem cycQ_decomp ', 'theorem cycQ_decompA '),
    ('cycQ_decomp hc', 'cycQ_decompA hc'),
    ('theorem cycQ_abs ', 'theorem cycQ_absA '),
    ('cycQ_abs hc', 'cycQ_absA hc'),
    ('theorem cycQ_ne_zero ', 'theorem cycQ_ne_zeroA '),
    ('cycQ_ne_zero hc', 'cycQ_ne_zeroA hc'),
    ('theorem N_ne_zero ', 'theorem N_ne_zeroA '),
    ('adj_zh hD hc', 'adj_zhA hD hc'),
    ('adj_wh hD hc', 'adj_whA hD hc'),
    ('section cycle2', 'section alt2'),
    ('end cycle2', 'end alt2'),
    ('section cycle', 'section alt'),
    ('end cycle', 'end alt'),
]


def conv(b):
    n_old = b.count(OLD)
    assert n_old > 0
    b = b.replace(OLD, NEW)
    for a, c in RENAMES:
        b = b.replace(a, c)
    assert 'IsCycle' not in b and 'node (' not in b, 'a use of the nodes is left'
    return b


b1 = conv(b1)
b2 = conv(b2)

HEAD = '''import DirectRoute.Cycle
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

'''

TAIL = r'''
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
'''

io.open(P + 'DirectRoute/Alt.lean', 'w', encoding='utf-8').write(HEAD + b1 + '\n' + b2 + TAIL)
print('wrote DefsB.lean and Alt.lean')
