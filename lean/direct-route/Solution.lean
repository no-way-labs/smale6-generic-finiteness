import DirectRoute.LemmaB
import DirectRoute.LemmaC
import DirectRoute.Relation
import DirectRoute.Degree
import DirectRoute.Cycle
import DirectRoute.Examples

/-!
The statements of `Challenge.lean` with their proofs. The definitions are in `DirectRoute/Defs.lean`.
-/

open Finset

/-- T1, Lemma B. `q` has sum 0 and `m` is its largest index with a nonzero entry. -/
theorem lemmaB (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ)
    (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (hm : m < n) (hqm : q m ≠ 0)
    (hsum : ∑ j ∈ range (m + 1), q j = 0)
    (hτ : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ) :
    ∑ j ∈ range (m + 1), (q j : ℝ) * u j ≠ 0 := lemmaB_proof n τ u q m hu hτ0 hm hqm hsum hτ

/-- T2, Lemma C. -/
theorem lemmaC (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hn : 2 ≤ n) (hτ : (n : ℝ) ^ 2 ≤ τ) (hu : Chamber n τ u)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    ¬ ∃ r f g, IsCycle (topPairs n u z w) (node n fun x y => (z x y : WithTop ℝ))
      (node n fun x y => (w x y : WithTop ℝ)) r f g := lemmaC_proof n τ u z w hτ hu hz hw

/-- T3, first half: every node of an edge of E* is the node of a second edge of E*. -/
theorem degree_two (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (e : ℕ × ℕ) (he : e ∈ D.Estar P) :
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dw e' = node (D.n + 1) D.dw e) ∧
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dz e' = node (D.n + 1) D.dz e) := degree_two_proof D P hD hP e he

/-- T3, second half: the graph B of a weight datum has a simple cycle. -/
theorem exists_cycle (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) :
    ∃ r f g, IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g := exists_cycle_proof D P hD hP

/-- T4: on every simple cycle of B, N Ψ* + q·u = 0 and N ≠ 0. -/
theorem cycle_relation (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 ∧
      cycN D.n r f g ≠ 0 := cycle_relation_proof D P τ hD hP hτ hu r f g hc

/-- T5: the bound on ζ_tl + ω_tl that Theorem D5′ uses. -/
theorem collision_bound (D : Datum) (τ : ℝ) (hD : D.IsWeightDatum)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (t l : ℕ) (htl : t < l) (hl : l < D.n) :
    D.z t l + D.w t l
      ≤ 2 * (2 * (D.n : ℝ) - 1) * (∑ j ∈ range D.n, |D.u j|) / 3 + 2 * D.u t + 2 * D.u l := collision_bound_proof D τ hD hτ hu t l htl hl

/-- E1: the chamber is not empty. -/
theorem chamber_nonempty (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : ∃ u, Chamber n τ u := chamber_nonempty_proof n τ hτ

/-- E2: `ex2` is a weight datum with Ψ* = −2 = −(2u_0 + 3u_1)/3, E* is the pair (0, 1) and the O-edge of
the body 1, they form a cycle, and N = −3, q = (−2, −3). -/
theorem ex2_spec :
    ex2.IsWeightDatum ∧ ex2.IsPsiStar (-2) ∧
    (∀ e, e ∈ ex2.Estar (-2) ↔ e = (0, 1) ∨ e = (1, 2)) ∧
    IsCycle (ex2.Estar (-2)) (node 3 ex2.dz) (node 3 ex2.dw) 1 (fun _ => (0, 1)) (fun _ => (1, 2)) ∧
    cycN 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) = -3 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 0 = -2 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 1 = -3 := Ex2.spec

/-- E3: `ex3` is a weight datum with Ψ* = 0; the O-edge of the body 1 is not in E*, that of the body 0 is. -/
theorem ex3_spec :
    ex3.IsWeightDatum ∧ ex3.IsPsiStar 0 ∧ (1, 3) ∉ ex3.Estar 0 ∧ (0, 3) ∈ ex3.Estar 0 := Ex3.spec

/-- E3c: `ex3c` is a weight datum, its weights lie in W_3(18) (18 = 2 n², the threshold of Theorem D4),
and Ψ* = −1. So the hypotheses of T3 to T5 hold together with an active gap inequality. -/
theorem ex3c_spec : ex3c.IsWeightDatum ∧ Chamber ex3c.n 18 ex3c.u ∧ ex3c.IsPsiStar (-1) := Ex3c.spec

/-- E3m: `ex3m` is a weight datum; the O-edges of the bodies 1 and 2 have no real Ψ; the term of
(1, O) is absent in colour z and present in colour w, and that of (2, O) the other way round. -/
theorem ex3m_spec :
    ex3m.IsWeightDatum ∧ ¬ex3m.IsEdge (1, 3) ∧ ¬ex3m.IsEdge (2, 3) ∧
    (1, 3) ∉ ex3m.termsZ {1} ∧ (1, 3) ∈ ex3m.termsW {1} ∧
    (2, 3) ∈ ex3m.termsZ {2} ∧ (2, 3) ∉ ex3m.termsW {2} := Ex3m.spec

/-- E4: outside the chamber Lemma C fails, and a simple cycle exists. Four bodies with the weights
(0, 0, 1, 1). The pairs (0, 1), (1, 2), (2, 3), (0, 3) form a simple cycle of the pairs with the
largest Ψ (referee R31). -/
theorem ex4_cycle :
    IsUltra 4 (fun x y => (ex4z x y : WithTop ℝ)) ∧ IsUltra 4 (fun x y => (ex4w x y : WithTop ℝ)) ∧
    IsCycle (topPairs 4 ex4u ex4z ex4w) (node 4 fun x y => (ex4z x y : WithTop ℝ))
      (node 4 fun x y => (ex4w x y : WithTop ℝ)) 2
      (fun i => if i = 0 then (0, 1) else (2, 3)) (fun i => if i = 0 then (1, 2) else (0, 3)) := ⟨Ex4.ultra_z, Ex4.ultra_w, Ex4.cycle⟩
