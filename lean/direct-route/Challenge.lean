import Mathlib

/-!
# The combinatorial half of the direct-route proof: definitions and statements

Source: `docs/allN-direct-route-second-read.md` (the brief), §2 and §5 to §7.
Task: `docs/allN-direct-route-lean-task.md`.

Conventions. The bodies are the numbers 0, …, n − 1. A vector is a function on ℕ. For n ≥ 2 its
coordinates are the values below n. `Chamber` also reads `u 0` and `u 1` on padded inputs at n < 2. In a weight datum the extra vertex O is the number n. An edge is a pair `(x, y)` with
`x < y`: a body pair if `y < n`, the O-edge of the body `x` if `y = n`. Heights of O-edges lie in
`WithTop ℝ`; the height `⊤` says that the position is 0.

This file declares no notation, no instance and no attribute.
-/

open Finset

noncomputable section

/-! ## The chamber and Lemma B (brief §5) -/

/-- The chamber W_n(τ). -/
def Chamber (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) : Prop :=
  u 0 < u 1 ∧ ∀ j, 2 ≤ j → j < n → τ * (u (j - 1) - u 0) < u j - u (j - 1)

/-- T1, Lemma B. `q` has sum 0 and `m` is its largest index with a nonzero entry. -/
theorem lemmaB (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ)
    (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (hm : m < n) (hqm : q m ≠ 0)
    (hsum : ∑ j ∈ range (m + 1), q j = 0)
    (hτ : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ) :
    ∑ j ∈ range (m + 1), (q j : ℝ) * u j ≠ 0 := sorry

/-! ## Ultrametrics, nodes, cycles (brief §2, §6) -/

/-- Symmetric ultrametric heights on the distinct vertices 0, …, N − 1: in every triangle the least of
the three values is attained at least twice (stated as: no side is below the least of the other two).
The triangle condition is checked on distinct vertices. The mathematical diagonal is ⊤; stored diagonal
entries are padding. -/
def IsUltra (N : ℕ) (d : ℕ → ℕ → WithTop ℝ) : Prop :=
  (∀ x y, x < N → y < N → d x y = d y x) ∧
  ∀ x y t, x < N → y < N → t < N → x ≠ y → y ≠ t → x ≠ t → min (d x y) (d y t) ≤ d x t

/-- The node of the pair `e = (x, y)`: the vertices `p` with `d x p ≥ d x y`, and `x` itself. -/
def node (N : ℕ) (d : ℕ → ℕ → WithTop ℝ) (e : ℕ × ℕ) : Finset ℕ :=
  (range N).filter fun p => p = e.1 ∨ d e.1 e.2 ≤ d e.1 p

/-- A simple cycle e_1, …, e_2r of the bipartite multigraph in which the edge `e ∈ E` joins the vertex
`NZ e` of one side to the vertex `NW e` of the other. Here e_{2i+1} = `f i` and e_{2i+2} = `g i` for
`i < r`: `f i` and `g i` meet in a vertex of the ω side, `g i` and `f (i + 1)` in one of the ζ side. -/
structure IsCycle (E : Set (ℕ × ℕ)) (NZ NW : ℕ × ℕ → Finset ℕ) (r : ℕ) (f g : ℕ → ℕ × ℕ) : Prop where
  pos : 1 ≤ r
  mem_f : ∀ i, i < r → f i ∈ E
  mem_g : ∀ i, i < r → g i ∈ E
  adj_w : ∀ i, i < r → NW (f i) = NW (g i)
  adj_z : ∀ i, i < r → NZ (g i) = NZ (f ((i + 1) % r))
  inj_f : ∀ i j, i < r → j < r → f i = f j → i = j
  inj_g : ∀ i j, i < r → j < r → g i = g j → i = j
  ne_fg : ∀ i j, i < r → j < r → f i ≠ g j
  inj_w : ∀ i j, i < r → j < r → NW (f i) = NW (f j) → i = j
  inj_z : ∀ i j, i < r → j < r → NZ (f i) = NZ (f j) → i = j

/-! ## Lemma C (brief §6): bodies only -/

/-- Ψ of a body pair. -/
def psiPair (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ := (z a b + w a b) / 2 - u a - u b

/-- E°: the pairs of bodies with the largest Ψ. -/
def topPairs (n : ℕ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ) : Set (ℕ × ℕ) :=
  {e | e.1 < e.2 ∧ e.2 < n ∧ ∀ a b, a < b → b < n → psiPair u z w a b ≤ psiPair u z w e.1 e.2}

/-- T2, Lemma C. -/
theorem lemmaC (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hn : 2 ≤ n) (hτ : (n : ℝ) ^ 2 ≤ τ) (hu : Chamber n τ u)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    ¬ ∃ r f g, IsCycle (topPairs n u z w) (node n fun x y => (z x y : WithTop ℝ))
      (node n fun x y => (w x y : WithTop ℝ)) r f g := sorry

/-! ## Weight data (brief §2) -/

/-- The data of a weight datum: the mass weights, ζ and ω on the body pairs, and ξ_t = ζ_tO, η_t = ω_tO. -/
structure Datum where
  n : ℕ
  u : ℕ → ℝ
  z : ℕ → ℕ → ℝ
  w : ℕ → ℕ → ℝ
  xi : ℕ → WithTop ℝ
  eta : ℕ → WithTop ℝ

namespace Datum

variable (D : Datum)

/-- ζ on distinct vertices, with ⊤ at (O, O). Body diagonals are padding. -/
def dz (x y : ℕ) : WithTop ℝ :=
  if x = D.n then (if y = D.n then ⊤ else D.xi y) else if y = D.n then D.xi x else (D.z x y : WithTop ℝ)

/-- ω on distinct vertices, with ⊤ at (O, O). Body diagonals are padding. -/
def dw (x y : ℕ) : WithTop ℝ :=
  if x = D.n then (if y = D.n then ⊤ else D.eta y) else if y = D.n then D.eta x else (D.w x y : WithTop ℝ)

/-- Ψ(t, O) = −ξ_t − η_t − u_t; used only when ξ_t and η_t are real. -/
def psiO (t : ℕ) : ℝ := -(D.xi t).untopD 0 - (D.eta t).untopD 0 - D.u t

/-- Ψ of an edge. -/
def psiE (e : ℕ × ℕ) : ℝ := if e.2 = D.n then D.psiO e.1 else psiPair D.u D.z D.w e.1 e.2

/-- The edges with a real Ψ: the body pairs, and the O-edges of the bodies with X_t ≠ 0 and Y_t ≠ 0. -/
def IsEdge (e : ℕ × ℕ) : Prop :=
  e.1 < e.2 ∧ (e.2 < D.n ∨ (e.2 = D.n ∧ D.xi e.1 ≠ ⊤ ∧ D.eta e.1 ≠ ⊤))

/-- `P` is Ψ*, the largest Ψ over the edges. -/
def IsPsiStar (P : ℝ) : Prop := (∀ e, D.IsEdge e → D.psiE e ≤ P) ∧ ∃ e, D.IsEdge e ∧ D.psiE e = P

/-- E*: the edges with Ψ = Ψ*. -/
def Estar (P : ℝ) : Set (ℕ × ℕ) := {e | D.IsEdge e ∧ D.psiE e = P}

/-- Φ^z of the term of the edge (t, y) in a cut identity of colour z (Lemma A); `t` is a body in the
set, `y` is a body outside it or O. -/
def phiZ (t y : ℕ) : ℝ :=
  if y = D.n then -D.u t - (D.xi t).untopD 0 else psiPair D.u D.z D.w t y + D.w t y

/-- Φ^w, the same in colour w. -/
def phiW (t y : ℕ) : ℝ :=
  if y = D.n then -D.u t - (D.eta t).untopD 0 else psiPair D.u D.z D.w t y + D.z t y

/-- The terms of C^z_S that are not 0: `(t, l)` with `t ∈ S` and `l` a body outside `S`, and `(t, O)`
with `t ∈ S` and X_t ≠ 0. -/
def termsZ (S : Finset ℕ) : Set (ℕ × ℕ) :=
  {e | e.1 ∈ S ∧ ((e.2 < D.n ∧ e.2 ∉ S) ∨ (e.2 = D.n ∧ D.xi e.1 ≠ ⊤))}

/-- The terms of C^w_S that are not 0. -/
def termsW (S : Finset ℕ) : Set (ℕ × ℕ) :=
  {e | e.1 ∈ S ∧ ((e.2 < D.n ∧ e.2 ∉ S) ∨ (e.2 = D.n ∧ D.eta e.1 ≠ ⊤))}

/-- The cut condition of colour z for `S`: the largest Φ^z is attained by two different terms. -/
def CutZ (S : Finset ℕ) : Prop :=
  ∃ e₁ e₂, e₁ ∈ D.termsZ S ∧ e₂ ∈ D.termsZ S ∧ e₁ ≠ e₂ ∧ D.phiZ e₁.1 e₁.2 = D.phiZ e₂.1 e₂.2 ∧
    ∀ e, e ∈ D.termsZ S → D.phiZ e.1 e.2 ≤ D.phiZ e₁.1 e₁.2

/-- The cut condition of colour w for `S`. -/
def CutW (S : Finset ℕ) : Prop :=
  ∃ e₁ e₂, e₁ ∈ D.termsW S ∧ e₂ ∈ D.termsW S ∧ e₁ ≠ e₂ ∧ D.phiW e₁.1 e₁.2 = D.phiW e₂.1 e₂.2 ∧
    ∀ e, e ∈ D.termsW S → D.phiW e.1 e.2 ≤ D.phiW e₁.1 e₁.2

/-- A weight datum: two ultrametrics on the n + 1 vertices and every cut condition. -/
structure IsWeightDatum : Prop where
  two : 2 ≤ D.n
  ultra_z : IsUltra (D.n + 1) D.dz
  ultra_w : IsUltra (D.n + 1) D.dw
  cut_z : ∀ S : Finset ℕ, S ⊆ range D.n → S.Nonempty → D.CutZ S
  cut_w : ∀ S : Finset ℕ, S ⊆ range D.n → S.Nonempty → D.CutW S

end Datum

/-! ## Theorem D4 (brief §7) -/

/-- The integer N of a cycle: 3 Σ (−1)^i over the body pairs e_i; `f i` has an odd place, `g i` an even one. -/
def cycN (n r : ℕ) (f g : ℕ → ℕ × ℕ) : ℤ :=
  3 * ∑ i ∈ range r, ((if (g i).2 < n then 1 else 0) - (if (f i).2 < n then 1 else 0))

/-- The contribution of an edge at an even place to the coefficient q_k: 2 for a body pair through `k`,
−1 for the O-edge of `k`. -/
def inc (n : ℕ) (e : ℕ × ℕ) (k : ℕ) : ℤ :=
  if e.2 < n then (if e.1 = k ∨ e.2 = k then 2 else 0) else (if e.1 = k then -1 else 0)

/-- The coefficient q_k of a cycle. -/
def cycQ (n r : ℕ) (f g : ℕ → ℕ × ℕ) (k : ℕ) : ℤ := ∑ i ∈ range r, (inc n (g i) k - inc n (f i) k)

/-- T3, first half: every node of an edge of E* is the node of a second edge of E*. -/
theorem degree_two (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (e : ℕ × ℕ) (he : e ∈ D.Estar P) :
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dw e' = node (D.n + 1) D.dw e) ∧
    (∃ e', e' ∈ D.Estar P ∧ e' ≠ e ∧ node (D.n + 1) D.dz e' = node (D.n + 1) D.dz e) := sorry

/-- T3, second half: the graph B of a weight datum has a simple cycle. -/
theorem exists_cycle (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P) :
    ∃ r f g, IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g := sorry

/-- T4: on every simple cycle of B, N Ψ* + q·u = 0 and N ≠ 0. -/
theorem cycle_relation (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 ∧
      cycN D.n r f g ≠ 0 := sorry

/-- T5: the bound on ζ_tl + ω_tl that Theorem D5′ uses. -/
theorem collision_bound (D : Datum) (τ : ℝ) (hD : D.IsWeightDatum)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (t l : ℕ) (htl : t < l) (hl : l < D.n) :
    D.z t l + D.w t l
      ≤ 2 * (2 * (D.n : ℝ) - 1) * (∑ j ∈ range D.n, |D.u j|) / 3 + 2 * D.u t + 2 * D.u l := sorry

/-! ## Tests of the definitions -/

/-- E1: the chamber is not empty. -/
theorem chamber_nonempty (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : ∃ u, Chamber n τ u := sorry

/-- The example n = 2 of the brief at u = (0, 2): ζ_01 = ω_01 = 0, ξ = η = (2, 0). -/
def ex2 : Datum where
  n := 2
  u := fun k => if k = 1 then 2 else 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 0 then ((2 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 0 then ((2 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)

/-- E2: `ex2` is a weight datum with Ψ* = −2 = −(2u_0 + 3u_1)/3, E* is the pair (0, 1) and the O-edge of
the body 1, they form a cycle, and N = −3, q = (−2, −3). -/
theorem ex2_spec :
    ex2.IsWeightDatum ∧ ex2.IsPsiStar (-2) ∧
    (∀ e, e ∈ ex2.Estar (-2) ↔ e = (0, 1) ∨ e = (1, 2)) ∧
    IsCycle (ex2.Estar (-2)) (node 3 ex2.dz) (node 3 ex2.dw) 1 (fun _ => (0, 1)) (fun _ => (1, 2)) ∧
    cycN 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) = -3 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 0 = -2 ∧
    cycQ 2 1 (fun _ => (0, 1)) (fun _ => (1, 2)) 1 = -3 := sorry

/-- A datum in a stratum: three bodies with equal mass weights, all real heights 0, and the body 1 at
the origin in both colours (the collinear configuration with the middle body at the centre of mass). -/
def ex3 : Datum where
  n := 3
  u := fun _ => 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)

/-- E3: `ex3` is a weight datum with Ψ* = 0; the O-edge of the body 1 is not in E*, that of the body 0 is. -/
theorem ex3_spec :
    ex3.IsWeightDatum ∧ ex3.IsPsiStar 0 ∧ (1, 3) ∉ ex3.Estar 0 ∧ (0, 3) ∈ ex3.Estar 0 := sorry

/-- A weight datum for three bodies over a chamber vector: u = (0, 1, 20), all heights of body pairs 0,
ξ = η = (1, 0, 0) (proposed by the reviewer of this file). -/
def ex3c : Datum where
  n := 3
  u := fun k => if k = 1 then 1 else if k = 2 then 20 else 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 0 then ((1 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 0 then ((1 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)

/-- E3c: `ex3c` is a weight datum, its weights lie in W_3(18) (18 = 2 n², the threshold of Theorem D4),
and Ψ* = −1. So the hypotheses of T3 to T5 hold together with an active gap inequality. -/
theorem ex3c_spec : ex3c.IsWeightDatum ∧ Chamber ex3c.n 18 ex3c.u ∧ ex3c.IsPsiStar (-1) := sorry

/-- A datum with the body 1 at the origin in colour z and the body 2 at the origin in colour w; equal
mass weights, all real heights 0 (proposed by the reviewer of this file). -/
def ex3m : Datum where
  n := 3
  u := fun _ => 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 2 then ⊤ else ((0 : ℝ) : WithTop ℝ)

/-- E3m: `ex3m` is a weight datum; the O-edges of the bodies 1 and 2 have no real Ψ; the term of
(1, O) is absent in colour z and present in colour w, and that of (2, O) the other way round. -/
theorem ex3m_spec :
    ex3m.IsWeightDatum ∧ ¬ex3m.IsEdge (1, 3) ∧ ¬ex3m.IsEdge (2, 3) ∧
    (1, 3) ∉ ex3m.termsZ {1} ∧ (1, 3) ∈ ex3m.termsW {1} ∧
    (2, 3) ∈ ex3m.termsZ {2} ∧ (2, 3) ∉ ex3m.termsW {2} := sorry

/-- The weights (0, 0, 1, 1) of the fourth test. -/
def ex4u : ℕ → ℝ := fun k => if 2 ≤ k then 1 else 0

/-- ζ of the fourth test: the cluster {1, 2, 3} at height 2, all other heights 0. -/
def ex4z : ℕ → ℕ → ℝ := fun x y => if 1 ≤ x ∧ 1 ≤ y then 2 else 0

/-- ω of the fourth test: the cluster {0, 2, 3} at height 2, all other heights 0. -/
def ex4w : ℕ → ℕ → ℝ := fun x y => if x ≠ 1 ∧ y ≠ 1 then 2 else 0

/-- E4: outside the chamber Lemma C fails, and a simple cycle exists. Four bodies with the weights
(0, 0, 1, 1). The pairs (0, 1), (1, 2), (2, 3), (0, 3) form a simple cycle of the pairs with the
largest Ψ (referee R31). -/
theorem ex4_cycle :
    IsUltra 4 (fun x y => (ex4z x y : WithTop ℝ)) ∧ IsUltra 4 (fun x y => (ex4w x y : WithTop ℝ)) ∧
    IsCycle (topPairs 4 ex4u ex4z ex4w) (node 4 fun x y => (ex4z x y : WithTop ℝ))
      (node 4 fun x y => (ex4w x y : WithTop ℝ)) 2
      (fun i => if i = 0 then (0, 1) else (2, 3)) (fun i => if i = 0 then (1, 2) else (0, 3)) := sorry

end
