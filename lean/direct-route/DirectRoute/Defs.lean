import Mathlib

/-!
The definitions of `Challenge.lean`, copied without change for the solution. The comparator checks that
they agree with the challenge.
-/

open Finset

noncomputable section

/-! ## The chamber and Lemma B (brief §5) -/

/-- The chamber W_n(τ). -/
def Chamber (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) : Prop :=
  u 0 < u 1 ∧ ∀ j, 2 ≤ j → j < n → τ * (u (j - 1) - u 0) < u j - u (j - 1)

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

/-! ## Tests of the definitions -/

/-- The example n = 2 of the brief at u = (0, 2): ζ_01 = ω_01 = 0, ξ = η = (2, 0). -/
def ex2 : Datum where
  n := 2
  u := fun k => if k = 1 then 2 else 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 0 then ((2 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 0 then ((2 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)

/-- A datum in a stratum: three bodies with equal mass weights, all real heights 0, and the body 1 at
the origin in both colours (the collinear configuration with the middle body at the centre of mass). -/
def ex3 : Datum where
  n := 3
  u := fun _ => 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)

/-- A weight datum for three bodies over a chamber vector: u = (0, 1, 20), all heights of body pairs 0,
ξ = η = (1, 0, 0) (proposed by the reviewer of this file). -/
def ex3c : Datum where
  n := 3
  u := fun k => if k = 1 then 1 else if k = 2 then 20 else 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 0 then ((1 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 0 then ((1 : ℝ) : WithTop ℝ) else ((0 : ℝ) : WithTop ℝ)

/-- A datum with the body 1 at the origin in colour z and the body 2 at the origin in colour w; equal
mass weights, all real heights 0 (proposed by the reviewer of this file). -/
def ex3m : Datum where
  n := 3
  u := fun _ => 0
  z := fun _ _ => 0
  w := fun _ _ => 0
  xi := fun t => if t = 1 then ⊤ else ((0 : ℝ) : WithTop ℝ)
  eta := fun t => if t = 2 then ⊤ else ((0 : ℝ) : WithTop ℝ)

/-- The weights (0, 0, 1, 1) of the fourth test. -/
def ex4u : ℕ → ℝ := fun k => if 2 ≤ k then 1 else 0

/-- ζ of the fourth test: the cluster {1, 2, 3} at height 2, all other heights 0. -/
def ex4z : ℕ → ℕ → ℝ := fun x y => if 1 ≤ x ∧ 1 ≤ y then 2 else 0

/-- ω of the fourth test: the cluster {0, 2, 3} at height 2, all other heights 0. -/
def ex4w : ℕ → ℕ → ℝ := fun x y => if x ≠ 1 ∧ y ≠ 1 then 2 else 0

end
