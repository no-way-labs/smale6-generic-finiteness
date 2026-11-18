import Challenge

/-!
# The statements of the paper that are stronger than those of `Challenge.lean`

Source: `paper/alln/main.tex` (the paper), Sections 4 to 6. This file uses the definitions of
`Challenge.lean` without change and adds one definition, `IsAltSeq`.

The paper states three things in a stronger form than `Challenge.lean`:

* Lemma 4.1 gives the sign of q·u, and `lemmaB` gives q·u ≠ 0 only;
* Lemma 5.2 excludes every closed alternating sequence (equal heights), and `lemmaC` excludes the
  simple cycles (equal nodes, distinct nodes) only;
* Theorem 6.2 (b), (c) is about every closed alternating sequence in E*, and `cycle_relation` is about
  the simple cycles only; Theorem 6.2 (d) bounds Ψ*, and `collision_bound` bounds ζ_tl + ω_tl only.

This file declares no notation, no instance and no attribute.
-/

open Finset

noncomputable section

/-- A closed alternating sequence (paper, Definition 5.1): 2r different edges
`f 0, g 0, …, f (r − 1), g (r − 1)` of `E`, such that `f i` and `g i` have the same height `HW`, and
`g i` and `f (i + 1)` have the same height `HZ`; the index after `r − 1` is 0. -/
structure IsAltSeq {α : Type} (E : Set (ℕ × ℕ)) (HZ HW : ℕ × ℕ → α) (r : ℕ) (f g : ℕ → ℕ × ℕ) :
    Prop where
  pos : 1 ≤ r
  mem_f : ∀ i, i < r → f i ∈ E
  mem_g : ∀ i, i < r → g i ∈ E
  adj_w : ∀ i, i < r → HW (f i) = HW (g i)
  adj_z : ∀ i, i < r → HZ (g i) = HZ (f ((i + 1) % r))
  inj_f : ∀ i j, i < r → j < r → f i = f j → i = j
  inj_g : ∀ i j, i < r → j < r → g i = g j → i = j
  ne_fg : ∀ i j, i < r → j < r → f i ≠ g j

/-! ## Lemma 4.1 with the sign -/

/-- Lemma 4.1: under the hypotheses of `lemmaB`, q·u has the sign of q_m. The statement says that the
product of q_m and q·u is positive. -/
theorem lemmaB_sign (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (q : ℕ → ℤ) (m : ℕ)
    (hu : Chamber n τ u) (hτ0 : 0 ≤ τ) (hm : m < n) (hqm : q m ≠ 0)
    (hsum : ∑ j ∈ range (m + 1), q j = 0)
    (hτ : (∑ j ∈ Ico 1 m, |(q j : ℝ)|) / |(q m : ℝ)| - 1 ≤ τ) :
    0 < (q m : ℝ) * ∑ j ∈ range (m + 1), (q j : ℝ) * u j := sorry

/-! ## Lemma 5.2: bodies only -/

/-- Lemma 5.2: over a chamber vector, E° contains no closed alternating sequence. The heights of a pair
`e` are `z e.1 e.2` and `w e.1 e.2`. -/
theorem lemmaC_alt (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hn : 2 ≤ n) (hτ : (n : ℝ) ^ 2 ≤ τ) (hu : Chamber n τ u)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    ¬ ∃ r f g, IsAltSeq (topPairs n u z w) (fun e => z e.1 e.2) (fun e => w e.1 e.2) r f g := sorry

/-- A simple cycle of the pairs of E° is a closed alternating sequence (paper, the paragraph after
Definition 5.1). So `lemmaC_alt` implies `lemmaC`. -/
theorem cycle_alt_bodies (n : ℕ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ))
    (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (topPairs n u z w) (node n fun x y => (z x y : WithTop ℝ))
      (node n fun x y => (w x y : WithTop ℝ)) r f g) :
    IsAltSeq (topPairs n u z w) (fun e => z e.1 e.2) (fun e => w e.1 e.2) r f g := sorry

/-! ## Theorem 6.2 (b), (c), (d) -/

/-- Theorem 6.2 (b) and (c): every closed alternating sequence in E* contains an O-edge, and its
numbers N and q satisfy N Ψ* + q·u = 0 and N ≠ 0. The heights of an edge `e` are `D.dz e.1 e.2` and
`D.dw e.1 e.2`, with values in `WithTop ℝ`. -/
theorem alt_relation (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g) :
    (∃ i, i < r ∧ ((f i).2 = D.n ∨ (g i).2 = D.n)) ∧
    (cycN D.n r f g : ℝ) * P + ∑ k ∈ range D.n, (cycQ D.n r f g k : ℝ) * D.u k = 0 ∧
      cycN D.n r f g ≠ 0 := sorry

/-- A simple cycle of the graph of E* is a closed alternating sequence. So `alt_relation` implies
`cycle_relation`. -/
theorem cycle_alt (D : Datum) (P : ℝ) (hD : D.IsWeightDatum) (r : ℕ) (f g : ℕ → ℕ × ℕ)
    (hc : IsCycle (D.Estar P) (node (D.n + 1) D.dz) (node (D.n + 1) D.dw) r f g) :
    IsAltSeq (D.Estar P) (fun e => D.dz e.1 e.2) (fun e => D.dw e.1 e.2) r f g := sorry

/-- Theorem 6.2 (d), the bound: Ψ* ≤ (2n − 1)(Σ |u_j|)/3. -/
theorem psi_star_bound (D : Datum) (P τ : ℝ) (hD : D.IsWeightDatum) (hP : D.IsPsiStar P)
    (hτ : 2 * (D.n : ℝ) ^ 2 ≤ τ) (hu : Chamber D.n τ D.u) :
    P ≤ (2 * (D.n : ℝ) - 1) * (∑ j ∈ range D.n, |D.u j|) / 3 := sorry

/-! ## Tests of the definition -/

/-- The two edges of E* of the example n = 2 form a closed alternating sequence. So the hypotheses of
`alt_relation` can hold. -/
theorem ex2_alt :
    IsAltSeq (ex2.Estar (-2)) (fun e => ex2.dz e.1 e.2) (fun e => ex2.dw e.1 e.2) 1
      (fun _ => (0, 1)) (fun _ => (1, 2)) := sorry

/-- Outside the chamber Lemma 5.2 fails: at the weights (0, 0, 1, 1) the pairs (0, 1), (1, 2), (2, 3),
(0, 3) form a closed alternating sequence in E°. -/
theorem ex4_alt :
    IsAltSeq (topPairs 4 ex4u ex4z ex4w) (fun e => ex4z e.1 e.2) (fun e => ex4w e.1 e.2) 2
      (fun i => if i = 0 then (0, 1) else (2, 3)) (fun i => if i = 0 then (1, 2) else (0, 3)) := sorry

end
