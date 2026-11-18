# Generic finiteness of planar central configurations for every n: a proof to be read

*2026-11-17. A brief for an independent reader. It is self-contained: the statement, every definition, and
the full proof are in this file. No other file of the repository is needed to judge the proof. §11 says what
the reader is asked to sign.*

## 0. What is asked

We have a proof of the following statement and we do not trust it yet.

> **Theorem.** For every n ≥ 2 there is a proper Zariski-closed subset of C^n, defined over Q, such that for
> positive masses (m_0, …, m_{n−1}) outside it the planar n-body problem has finitely many central
> configurations up to similarity.

For n ≥ 6 we know no published proof of this. The proof below is short (it fits in this file) and uses no
computation. A short proof of a statement of this size is more likely to hide an error than to be right, and
the reader should start from that position.

The state of the checks:

- The proof was written on 2026-11-17 and read once by a referee with no earlier context. The verdict was
  "sound with fixes"; the fixes are in this version. The referee did not know the literature on central
  configurations and did not search it.
- Float computations for n = 3, 4, 5 agree with the main combinatorial theorem (§9). They are evidence and
  no part of the proof.
- One part of the proof (Lemma C, the case of a balanced cycle) cannot be tested by any computation below
  six bodies, because the objects it excludes do not exist there.

**The request.** Read §1 to §8 and fill in the sheet of §11: for each of the items S1 to S9, say whether it
holds, holds with a fix, fails, or was not checked. If a step fails, give the first sentence that fails. If
you know a family of central configurations that contradicts one of the statements of §8, that settles the
matter and is the most useful thing you can tell us.

**Three places where we would look first.**

1. Lemma C, step (c): the inequality that excludes a "corner". The whole theorem rests on it for n ≥ 6.
2. Proposition D2: the passage from "the valuation of X_tl Y_tl is bounded above at every solution" to "X_tl Y_tl
   is constant on a component". It is the valuation form of the argument of Albouy and Kaloshin that on a
   continuum some mutual distance tends to zero.
3. The form over K of the theorem (§8): it is stronger than the theorem and it is where a counterexample
   from the literature would show.

## 1. The system and the statement in coordinates

**Central configurations.** Points z_0, …, z_{n−1} ∈ C, pairwise distinct, with masses m_t, form a central
configuration if λ (z_t − c) = Σ_{l ≠ t} m_l (z_t − z_l)/|z_t − z_l|³ for all t, with one real λ and one c.
For positive masses λ > 0: the inner product with m_t (z_t − c), summed over t, gives λ I = U with
I = Σ m_t |z_t − c|² and U = Σ_{t<l} m_t m_l/|z_t − z_l|. So a translation gives c = 0 and a scaling gives
λ = 1. What is left of the similarities is the rotations and the reflection.

**The system N_n** (the coordinates of Albouy and Kaloshin). Unknowns X_t, Y_t for t = 0, …, n − 1 and
P_tl = P_lt for t ≠ l. Write X_tl = X_t − X_l and Y_tl = Y_t − Y_l. The equations are

    (N1)  P_tl² X_tl Y_tl = 1,
    (N2)  X_t = Σ_{l ≠ t} m_l P_tl³ X_tl,
    (N3)  Y_t = Σ_{l ≠ t} m_l P_tl³ Y_tl.

A normalised central configuration gives the solution X_t = z_t, Y_t = z̄_t, P_tl = 1/|z_t − z_l|. The group
G = {λ ≠ 0} acts on the solutions by X ↦ λX, Y ↦ λ⁻¹Y, P ↦ P; the rotations of the plane are the elements
|λ| = 1. We call this action the rotation. Two normalised central configurations that give solutions in one
G-orbit differ by a rotation of the plane: if z′_t = λ z_t and z̄′_t = λ⁻¹ z̄_t then |λ| = 1.

So the theorem of §0 follows from:

> **Theorem D5.** For every n ≥ 2 there is a proper Zariski-closed subset of C^n, defined over Q, such that
> for masses outside it N_n has finitely many solutions modulo the rotation.

Masses are complex here. A proper Zariski-closed subset of C^n meets R^n in a proper real algebraic subset,
so the theorem of §0 covers positive masses outside a set of measure zero. The proof does not describe the
closed subset and gives no bound on the number of solutions.

**First facts about a solution** (over any field that contains the masses).

- (F1) X_tl, Y_tl and P_tl are not 0, by (N1). So at most one X_t is 0 and at most one Y_t is 0.
- (F2) The rotation acts freely: λ X_ab = X_ab and X_ab ≠ 0 give λ = 1.

## 2. Valuations, trees, and the values Ψ

**The field K.** Let K be the field of Hahn series Q̄((T^R)): formal sums Σ a_γ T^γ with a_γ ∈ Q̄, real
exponents γ and a well-ordered support. K is algebraically closed (it is maximally complete with a divisible
value group and an algebraically closed residue field of characteristic 0). Its valuation v: K^* → R is the
least exponent; v(0) = +∞. Every real number is the valuation of infinitely many elements of K.

**Mass weights.** For masses m_t ∈ K^* put u_t = v(m_t). A larger u_t is a lighter body. Name the bodies so
that u_0 ≤ u_1 ≤ … ≤ u_{n−1}; body 0 is the heaviest.

**Weights of a solution.** For a solution of N_n over K put

    ξ_t = v(X_t),   η_t = v(Y_t),   ζ_tl = v(X_tl),   ω_tl = v(Y_tl).

By (F1), ζ_tl and ω_tl are real; ξ_t and η_t are real or +∞, and +∞ occurs for at most one body in each
colour. We call the X side colour z and the Y side colour w. By (N1), v(P_tl) = −(ζ_tl + ω_tl)/2.

**The leaf O.** Add to the n bodies one more vertex O, the origin, and put ζ_tO = ξ_t and ω_tO = η_t. Then
ζ_xy is the valuation of the difference of two of the n + 1 elements X_0, …, X_{n−1}, 0 of K. So ζ is an
**ultrametric** on the n + 1 vertices: in every triangle the least of the three values is attained at least
twice. The same holds for ω. The **edges** are the pairs of the n + 1 vertices: the body pairs (t, l) and
the O-edges (t, O).

**The tree of an ultrametric.** Let d be an ultrametric on a finite set Λ with values in R ∪ {+∞}, and put
d_xx = +∞. For x ≠ y the **node** of the pair {x, y} is the set N(x, y) = {p ∈ Λ : d_xp ≥ d_xy}. It contains x
and y, it does not change if x and y are exchanged, and d_pp′ ≥ d_xy for all p, p′ in it; d_xy is its
**height**. The **children** of a node N of height h are the classes of the equivalence relation d_pp′ > h on
N. The following hold, each by one use of the triangle condition.

- (T1) If p and p′ lie in different children of N, then d_pp′ = h.
- (T2) If p ∈ N and p′ ∉ N, then d_pp′ < h.
- (T3) Two nodes are disjoint or one contains the other.
- (T4) If p, p′ ∈ N and d_pp′ = h, then N(p, p′) = N.

We speak of the ζ-node and the ω-node of an edge e, and of their heights ζ_e and ω_e.

**The values Ψ.** For a body pair and for an O-edge put

    Ψ(t, l) = (ζ_tl + ω_tl)/2 − u_t − u_l,      Ψ(t, O) = −ξ_t − η_t − u_t   (−∞ if X_t = 0 or Y_t = 0).

Ψ(e) is minus the valuation of a term of I − U, where I = Σ m_t X_t Y_t and U = Σ_{t<l} m_t m_l P_tl: the
term m_t m_l P_tl has the valuation −Ψ(t, l) and the term m_t X_t Y_t has the valuation −Ψ(t, O). Let

    Ψ* = the largest Ψ(e) over all edges,      E* = the set of the edges with Ψ(e) = Ψ*.

Ψ* is a real number, because the body pairs have real values and n ≥ 2.

**Lemma A (the cut identities and their values).** Let S be a nonempty set of bodies. At every solution of
N_n,

    C^z_S:   Σ_{t ∈ S} m_t X_t − Σ_{t ∈ S, l ∉ S} m_t m_l P_tl³ X_tl = 0,

and the same with Y in place of X (C^w_S). The terms of C^z_S are one for each edge that joins S to its
complement in the n + 1 vertices. Every partition of the n + 1 vertices into two nonempty sides has one
side without O, so it has one identity in each colour. At a solution over K:

- the term of a body pair (t, l) in C^z_S has the valuation −Φ^z(t, l), with Φ^z(t, l) = Ψ(t, l) + ω_tl;
- the term of (t, O) in C^z_S is 0 if X_t = 0; otherwise it has the valuation −Φ^z(t, O), with
  Φ^z(t, O) = −u_t − ξ_t, and this is Ψ(t, O) + η_t if Y_t ≠ 0;
- **the cut condition:** among the terms of C^z_S that are not 0, the largest value Φ^z is attained at least
  twice.

The same holds in colour w with Φ^w(t, l) = Ψ(t, l) + ζ_tl and Φ^w(t, O) = −u_t − η_t.

*Proof.* Multiply (N2) for the body t by m_t and add over t ∈ S. A pair {t, l} inside S contributes
m_t m_l P_tl³ (X_tl + X_lt) = 0. This gives C^z_S. The valuation of m_t m_l P_tl³ X_tl is
u_t + u_l − 3(ζ_tl + ω_tl)/2 + ζ_tl = −(Ψ(t, l) + ω_tl), and that of m_t X_t is u_t + ξ_t. The terms are
elements of K with sum 0, so the least valuation among the terms that are not 0 is attained at least
twice. ∎

**Weight data.** The combinatorial part of the proof (§6, §7) uses only the following. A **weight datum** is
a vector u ∈ R^n and two ultrametrics ζ, ω on the n + 1 vertices, with real values on the body pairs and
values in R ∪ {+∞} on the O-edges, such that the cut condition of Lemma A holds for every nonempty set S of
bodies and both colours. Here ξ_t = ζ_tO and η_t = ω_tO, and the term of (t, O) counts as 0 in colour z when
ξ_t = +∞ and in colour w when η_t = +∞. By Lemma A the weights of a solution over K form a weight datum.

**Example, n = 2.** Here P³ (m_0 + m_1) = 1 (Kepler's third law). With u_0 < u_1 this gives
ζ_01 + ω_01 = 2u_0/3, ξ_1 = ζ_01, ξ_0 = ζ_01 + u_1 − u_0, and the same for η. So
Ψ(0, 1) = Ψ(1, O) = −(2u_0 + 3u_1)/3 and Ψ(0, O) is smaller by u_1 − u_0.

## 3. Lemma D0: a continuum at generic masses gives a component of dimension 2 over K

**Lemma D0.** Suppose that the set of masses m ∈ C^n at which N_n has infinitely many solutions modulo the
rotation lies in no proper Zariski-closed subset of C^n. Let u* ∈ R^n have Q-linearly independent
coordinates. Then the solution set of N_n over K at the masses m_t = T^{u*_t} has an irreducible component of
dimension at least 2.

*Proof.* (i) Fix masses in an algebraically closed field. The solution set is a closed subset of an affine
space. The group G is connected, so it maps every irreducible component to itself, and it acts freely (F2),
so every orbit has dimension 1 and every component has dimension at least 1. A component of dimension 1 is
one orbit: every orbit in it is constructible and dense in it, and two such sets meet. So there are
infinitely many orbits if and only if some component has dimension at least 2.

(ii) Let 𝒳 be the set of the pairs (masses, solution), a closed subset of an affine space, defined over Q.
The set 𝒳₂ of the points of 𝒳 at which the fibre over the masses has local dimension at least 2 is closed
(semicontinuity of the dimension of a fibre) and defined over Q. By (i) the set of the hypothesis is the
image of 𝒳₂ in C^n. It is constructible (Chevalley).

(iii) A constructible set that lies in no proper closed subset contains a dense open set, so the fibre of 𝒳₂
over the generic point of the mass space is not empty. So over an algebraic closure of Q(m) the solution set
of N_n at the generic masses has a component of dimension at least 2.

(iv) The map m_t ↦ T^{u*_t} sends a polynomial Σ h_α m^α to Σ h_α T^{u*·α}. The exponents u*·α are distinct for
distinct α, so the image is 0 only if the polynomial is 0. So the map extends to an embedding of Q(m), and
then of its algebraic closure, in K. An irreducible variety over an algebraically closed field stays
irreducible of the same dimension over a larger algebraically closed field. ∎

## 4. Proposition D2: no collision at the K-points implies finiteness

**Proposition D2.** Let m ∈ (K^*)^n. Suppose there is a real number M such that ζ_tl + ω_tl ≤ M for every
solution of N_n over K at the masses m and every body pair {t, l}. Then the solution set of N_n over K at the
masses m has no irreducible component of dimension at least 2.

In words: v(X_tl Y_tl) is the valuation of the squared mutual distance, and a large valuation is a
collision. If no pair of bodies collides beyond a fixed order at any solution over K, there is no continuum.

*Proof.* Let V be an irreducible component of dimension at least 2. Its points over K are solutions.

*Every X_tl Y_tl is constant on V.* Fix a body pair and let g = X_tl Y_tl, a regular function on V. V is
irreducible, so the closure of g(V) in the affine line is irreducible: g is constant, or g(V) contains all
of K but finitely many elements. In the second case g(V) contains elements of every valuation, so some
solution in V has ζ_tl + ω_tl = v(g) > M. This is excluded. So g is a constant d_tl, and d_tl ≠ 0 by (F1).

*Every P_tl is constant on V.* P_tl² = 1/d_tl has two solutions and V is irreducible.

*V is finite modulo the rotation.* G is connected, so it maps V to itself. Fix two bodies a, b. Every orbit
in V has one point with X_ab = 1. So the set V₁ of the points of V with X_ab = 1 has dimension at least
dim V − 1 ≥ 1. On V₁, Y_ab = d_ab. For a third body c, X_cb = X_ca + 1 and Y_cb = Y_ca + d_ab. So

    X_ca Y_ca = d_ca   and   (X_ca + 1)(Y_ca + d_ab) = d_cb,

which give Y_ca = d_cb − d_ca − d_ab − d_ab X_ca and then

    −d_ab X_ca² + (d_cb − d_ca − d_ab) X_ca − d_ca = 0.

The leading coefficient is not 0, so X_ca and Y_ca take at most two values each on V₁. So every difference
X_tl, Y_tl takes finitely many values on V₁, every P_tl is constant, and (N2), (N3) give the positions X_t, Y_t
from these. So V₁ is finite. This contradicts dim V₁ ≥ 1. ∎

The proof uses no tropical geometry: no balancing, no theorem on the dimension of a tropical variety. A
component on which bodies only separate, or on which one position tends to 0, is excluded together with
the others, because on a component of dimension 2 some X_tl Y_tl takes every value.

## 5. The chamber and Lemma B

For τ ≥ 0 let

    W_n(τ) = { u ∈ R^n : u_1 > u_0 and u_j − u_{j−1} > τ (u_{j−1} − u_0) for j = 2, …, n − 1 }.

It is an open cone and it is not empty. In W_n(τ) the mass weights increase, and each gap is more than τ
times the whole range below it. In terms of masses: every body is lighter than the one before it by a
large power.

**Lemma B (hyperplane).** Let q ∈ Z^n be nonzero with Σ q_j = 0, and let m be the largest index with q_m ≠ 0.
If u ∈ W_n(τ) and τ ≥ (Σ_{1 ≤ j < m} |q_j|)/|q_m| − 1, then q·u ≠ 0.

*Proof.* Σ q_j = 0 gives q·u = Σ_{j ≥ 1} q_j (u_j − u_0), and m ≥ 1. If m = 1 this is q_1 (u_1 − u_0) ≠ 0. Let
m ≥ 2 and q·u = 0. Then |q_m| (u_m − u_0) ≤ (Σ_{1 ≤ j < m} |q_j|)(u_{m−1} − u_0), because u_j − u_0 ≤ u_{m−1} − u_0
for j < m. In W_n(τ), u_m − u_0 > (1 + τ)(u_{m−1} − u_0) > 0. So (1 + τ)|q_m| < Σ_{1 ≤ j < m} |q_j|. ∎

## 6. Lemma C: the graph of the largest Ψ on the bodies has no cycle

This section is about the bodies only; O does not occur. Let ζ, ω be two ultrametrics on the n bodies with
real values and let u ∈ R^n. No cut condition is assumed. Put Ψ(a, b) = (ζ_ab + ω_ab)/2 − u_a − u_b, let Ψ° be
the largest value and E° the set of the pairs that attain it. For e ∈ E° let Z_e and W_e be its ζ-node and
its ω-node (sets of bodies). Let B° be the bipartite multigraph with one vertex for each ζ-node, one vertex
for each ω-node, and one edge for each e ∈ E°, between Z_e and W_e.

A **simple cycle** of a bipartite multigraph is a cyclic sequence e_1, …, e_2r of distinct edges, r ≥ 1,
through 2r distinct vertices, each vertex on two consecutive edges. We number it so that e_1 and e_2 meet
in an ω-node, e_2 and e_3 in a ζ-node, and so on, and e_2r and e_1 in a ζ-node.

**Lemma C.** Let n ≥ 2, τ ≥ n² and u ∈ W_n(τ). Then B° has no simple cycle.

*Proof.* Suppose C = e_1, …, e_2r is a simple cycle, e_i = (a_i, b_i).

*(C1) A pair of E° is the two heaviest bodies of its two nodes.* Let e = (c, d) ∈ E° and let a be another
body of Z_e ∩ W_e. Then ζ_ca ≥ ζ_cd and ω_ca ≥ ω_cd, so

    Ψ° ≥ Ψ(c, a) ≥ (ζ_cd + ω_cd)/2 − u_c − u_a = Ψ° + u_d − u_a,

and u_a ≥ u_d. In the same way u_a ≥ u_c. The mass weights are distinct, so a is lighter than c and d. So
two different pairs of E° do not have the same ζ-node and the same ω-node, and r ≥ 2.

*(C2) The cycle is balanced.* Consecutive edges share the height of their common node, so
Σ_i (−1)^i ω_{e_i} = 0 and Σ_i (−1)^i ζ_{e_i} = 0. Every Ψ(e_i) is Ψ° and the number of edges is even. So
q·u = 0 for q = Σ_i (−1)^i (1_{a_i} + 1_{b_i}). The coefficients of q are integers with sum 0, and |q_j| ≤ n − 1
because a body lies in at most n − 1 pairs. If q ≠ 0, Lemma B gives τ < (n − 2)(n − 1) − 1 < n². So q = 0:
every body lies in as many pairs e_i with i even as with i odd.

*(C3) The heights on the cycle.* For an edge e = (a, b) of C between the ζ-node z and the ω-node w, with
heights h_z and g_w, the definition of Ψ gives h_z + g_w − 2Ψ° = 2(u_a + u_b). For a ζ-node z and an ω-node w
of C take a path of C from z to w, with edges f_1, …, f_{2s+1}, and put
σ(z, w) = Σ_i (−1)^{i+1} (1_a + 1_b)(f_i). The heights of the inner nodes of the path cancel in the
alternating sum, so

    h_z + g_w − 2Ψ° = 2 σ(z, w)·u.

The two paths of C from z to w give vectors that differ by ±q = 0, so σ(z, w) does not depend on the path.
Its coefficients are integers with sum 2.

*(C4) The inequality (P).* Let z, w be nodes of C and let p ≠ p′ be two bodies of Z ∩ W (the sets of z and
w). Then ζ_pp′ ≥ h_z and ω_pp′ ≥ g_w, so 2Ψ° ≥ 2Ψ(p, p′) ≥ h_z + g_w − 2u_p − 2u_p′. With (C3):

    (1_p + 1_p′ − σ(z, w))·u ≥ 0.

*(C5) The lightest body of C.* Let L be the lightest body that lies in a pair of C (the largest name), and
let e^1, …, e^m be the pairs of C that contain L, e^i = (L, x_i), with nodes Z_i and W_i. By (C2), m is even
and m ≥ 2. The x_i are distinct, and they are heavier than L.

*(a) Staircase.* The sets Z_i all contain L, so by (T3) they form a chain; so do the W_i. Suppose Z_j ⊆ Z_i
and W_j ⊆ W_i for some i ≠ j. Then x_j ∈ Z_i ∩ W_i. By (C1), L and x_i are the two heaviest bodies of
Z_i ∩ W_i, so x_j is lighter than L. But x_j lies in a pair of C. So this does not occur. So the Z_i are
distinct, the W_i are distinct, and the pairs can be numbered with

    Z_1 ⊋ Z_2 ⊋ … ⊋ Z_m   and   W_1 ⊊ W_2 ⊊ … ⊊ W_m.

*(b) Levels.* There is an integer function ℓ on the 2r nodes of C such that for every edge e of C, between
the ζ-node z and the ω-node w, ℓ(z) − ℓ(w) = 1 if L ∈ e and ℓ(z) = ℓ(w) otherwise. To see this, go once
around C. The edge e_i is passed from its ζ-node to its ω-node if i is odd and the other way if i is even.
So the total change of ℓ is the number of the pairs with L at even places minus the number at odd places,
which is 0 by (C2). Around C the value of ℓ changes at the m pairs e^i only, by +1 at half of them and by
−1 at the other half. So

    max ℓ − min ℓ ≤ m/2.

For a ζ-node z and an ω-node w of C the coefficient of 1_L in σ(z, w) is ℓ(z) − ℓ(w): both count the edges
with L on a path from z to w with alternating signs.

*(c) Corners.* Let i < j. The set Z_i ∩ W_j contains L, x_i (because x_i ∈ W_i ⊂ W_j) and x_j (because
x_j ∈ Z_j ⊂ Z_i). So it has at least two bodies heavier than L, and its two heaviest bodies p, p′ are heavier
than L. By (C4), v·u ≥ 0 for v = 1_p + 1_p′ − σ(z_i, w_j). The coefficients of v are integers with sum 0 and
|v_k| ≤ n. They are 0 at the bodies lighter than L, because those bodies lie in no pair of C and are not p
or p′. The coefficient at L is v_L = −(ℓ(z_i) − ℓ(w_j)). Here L ≥ 2 as a name, because x_i and x_j are two
bodies heavier than L. Suppose ℓ(z_i) − ℓ(w_j) ≥ 1. Then, as in Lemma B,

    v·u = Σ_{1 ≤ k ≤ L} v_k (u_k − u_0) ≤ v_L (u_L − u_0) + (Σ_{1 ≤ k < L} |v_k|)(u_{L−1} − u_0)
        < ( −(1 + τ) + (n − 2) n ) (u_{L−1} − u_0) ≤ 0   for τ ≥ n² − 2n − 1.

This contradicts v·u ≥ 0. So ℓ(z_i) ≤ ℓ(w_j) for all i < j.

*(d) The count.* The pair e^i contains L, so ℓ(z_i) = ℓ(w_i) + 1. With (c), ℓ(w_j) ≥ ℓ(z_i) = ℓ(w_i) + 1 for
i < j. So ℓ(w_m) ≥ ℓ(w_1) + m − 1 and ℓ(z_m) ≥ ℓ(w_1) + m. Then max ℓ − min ℓ ≥ m > m/2, against (b). ∎

A remark for the reader. A balanced simple cycle needs at least six bodies: at n ≤ 5 an enumeration of all
pairs of trees finds none, and at n = 6 there are 96 (hexagons on all six bodies). So for n ≤ 5 only (C1)
and (C2) are in use, and the steps (C3) to (C5) carry the theorem from n = 6 on.

## 7. Theorem D4: the largest Ψ takes finitely many values

Let a weight datum (u, ζ, ω) be given (§2), with Ψ, Ψ*, E* as in §2. Let B be the bipartite multigraph with
one vertex for each ζ-node and each ω-node of the trees on the n + 1 vertices, and one edge for each
e ∈ E*, between the ζ-node and the ω-node of e. An edge of E* has a real value Ψ, so its two nodes have real
heights.

**Theorem D4.** Let n ≥ 2, τ ≥ 2n² and u ∈ W_n(τ). For every weight datum over u, the graph B has a simple
cycle, and every simple cycle e_1, …, e_2r of B gives

    N Ψ* + q·u = 0,   with   N = 3 Σ_{i : e_i a body pair} (−1)^i ≠ 0,
    q = Σ_{i : e_i = (a, b)} 2 (−1)^i (1_a + 1_b) − Σ_{i : e_i = (t, O)} (−1)^i 1_t.

So Ψ* is one of finitely many numbers that depend on u only, and Ψ* ≤ (2n − 1)(|u_0| + … + |u_{n−1}|)/3.

*Proof.*

*Step 1: every vertex of B that meets an edge has degree at least 2.* Let e ∈ E* and let v be its ω-node,
of height ω_v = ω_e, a real number. Let S′ be a union of children of v that contains one end of e and not
the other. Let S be the one of S′ and its complement that does not contain O. The terms of C^z_S are the
edges between S′ and its complement. Let f = (x, y) be such an edge, x ∈ S′.

- If the term of f is 0, it plays no part in the cut condition.
- If f = (r, O) with Y_r = 0 (that is, η_r = +∞): then ω_rO = +∞ is larger than the real number ω_v, so r and
  O lie in one child of v or both outside v. Then f does not join S′ to its complement. So this case does
  not occur.
- In every other case Φ^z(f) = Ψ(f) + ω_f. If y ∈ v then x and y lie in different children of v and ω_f = ω_v
  by (T1). If y ∉ v then ω_f < ω_v by (T2). So Φ^z(f) ≤ Ψ* + ω_v, with equality if and only if f ∈ E* and
  ω_f = ω_v. By (T4), ω_f = ω_v says that the ω-node of f is v.

The edge e is one of these edges, its term is not 0, and it attains Ψ* + ω_v. By the cut condition a second
edge attains it. So v lies on at least two edges of B. The same argument with the colour w and the ζ-node
gives the other half.

*Step 2: the relation of a cycle.* E* is not empty, so by Step 1 the graph B has a simple cycle
e_1, …, e_2r, numbered as in §6. Consecutive edges share the height of their common node, so
Σ_i (−1)^i (ζ_{e_i} + ω_{e_i}) = 0. On E*,

    ζ_e + ω_e = 2Ψ* + 2u_a + 2u_b   for a body pair (a, b),      ζ_e + ω_e = −Ψ* − u_t   for an O-edge (t, O).

Put S_p = Σ_{body pairs} (−1)^i and S_O = Σ_{O-edges} (−1)^i. The sum above is (2S_p − S_O) Ψ* + q·u = 0. The
cycle has as many edges at even places as at odd places, so S_p + S_O = 0, and 2S_p − S_O = 3S_p = N. Also
Σ_j q_j = 4S_p − S_O = 5N/3.

*Step 3: a simple cycle of B has an O-edge.* Suppose all e_i are body pairs. Restrict ζ and ω to the bodies.
Then Ψ* is attained by a body pair, so Ψ° = Ψ* and the e_i lie in E°. The ζ-node of a body pair on the bodies
is its ζ-node on the n + 1 vertices with O left out. Two body pairs have the same ζ-node on the n + 1
vertices if and only if they have the same ζ-node on the bodies: if the two nodes contain the same bodies,
then each contains both pairs, so by (T3) one contains the other, and a node that contains a pair contains
the node of that pair. The same holds for ω. So e_1, …, e_2r is a simple cycle of B°. Lemma C
excludes it, because τ ≥ n².

*Step 4: N ≠ 0.* By Step 3 the cycle has an O-edge (t, O), at some place i_0. The edges of the cycle are
distinct, so (t, O) occurs once. So q_t = 2 Σ_{i : t ∈ e_i a body pair} (−1)^i − (−1)^{i_0} is odd, and q ≠ 0.
Suppose N = 0. Then Σ_j q_j = 0. Also |q_j| ≤ 2(n − 1) + 1, because a body lies in at most n − 1 body pairs
and one O-edge. Lemma B then gives τ < (n − 2)(2n − 1) − 1 = 2n² − 5n + 1 < 2n². So N ≠ 0.

*The bound.* Ψ* = −q·u/N with |N| ≥ 3 and |q_j| ≤ 2n − 1. The pairs (N, q) range over a finite set that
depends on n only. ∎

Two remarks.

- For n = 2 the cycle is (0, 1), (1, O), with N = −3 and q = (−2, −3). This is the example of §2.
- The hypothesis on u is needed. At u = (0, 1, 2, 3) a float search finds weight data with the cycle
  (0, 2), (2, O), (0, O), (0, 3), for which N = 0, q = (1, 0, −3, 2), q·u = 0, and Ψ* is as large as one
  likes. Lemma B excludes this q in W_4(τ) for τ ≥ 1/2. With equal mass weights there are cycles of body
  pairs.

## 8. Theorem D5 and its form over K

**Theorem D5′ (the form over K).** Let n ≥ 2 and let m ∈ (K^*)^n have mass weights u = v(m) ∈ W_n(2n²). Then
N_n has finitely many solutions over K modulo the rotation.

*Proof.* By Lemma A the weights of a solution over K form a weight datum over u. By Theorem D4,
Ψ* ≤ M_0 := (2n − 1) Σ |u_j|/3 at every solution. Every body pair is an edge, so
ζ_tl + ω_tl = 2Ψ(t, l) + 2u_t + 2u_l ≤ 2M_0 + 2u_t + 2u_l. Proposition D2 applies with M = 2M_0 + 4 max |u_j|:
no component has dimension at least 2. By part (i) of the proof of Lemma D0, which holds over K, there are
finitely many orbits. ∎

**Proof of Theorem D5.** W_n(2n²) is open and not empty, so it contains a vector u* with Q-linearly
independent coordinates. If the set of masses with infinitely many solutions modulo the rotation lay in no
proper closed subset of C^n, Lemma D0 would give a component of dimension at least 2 over K at the masses
T^{u*_t}, against Theorem D5′. The set is constructible and defined over Q (Lemma D0, (ii)), so its closure is
a proper closed subset defined over Q. ∎

**What Theorem D5′ says about the bad masses** (a remark; the proof of Theorem D5 does not use it). No mass
vector over K with a continuum has its vector of valuations in W_n(2n²), nor in the image of W_n(2n²) under
a permutation of the bodies. Let Σ be the closure of the set of masses with a continuum. The points over K
with a given valuation are Zariski dense in a variety whose tropicalisation contains that valuation
(Payne), so the tropicalisation of Σ misses these open cones. **A family of masses with a known continuum of
central configurations, which has a point over a field of series with strongly hierarchical valuations,
would refute the proof.** The example we know does not: Roberts' continuum for five bodies has the masses
(1, 1, 1, 1, −1/4) up to a common factor, and the tropicalisation of the line through this vector is the
line R (1, …, 1), which meets none of the open cones.

**What the proof does not use.** The torque identities, the positivity of the masses, the dimension of the
ambient space beyond the plane, any classification of singular diagrams, any computation.

**Where each hypothesis enters.**

| hypothesis | used in |
|---|---|
| the exponent 3 of P in (N2), (N3) | Step 2 (the coefficient 3 in N) and Step 4 (parity: a body pair contributes an even number to q_t and an O-edge contributes ±1) |
| the left sides X_t, Y_t of (N2), (N3) | the O-edges. If the left sides are λX_t, λY_t with a free λ, Step 2 gets the extra term (N/3) v(λ), Ψ* is not bounded, and the system has a continuum |
| every pair of bodies interacts | the last line of Theorem D5′: every body pair is an edge of the cuts that separate it |
| u ∈ W_n(2n²) | Lemma B in (C2), (c) of (C5) and Step 4 |

## 9. Evidence so far (no part of the proof)

All LP computations are in floating point with no certificates.

- **Solutions.** All 114 solutions of N_3 modulo the rotation (54 of Lagrange type, 60 collinear) were computed
  at four numerically hierarchical mass vectors to 440 to 3,800 digits. Their valuations form weight data;
  at every solution E* = {(0, 1), (1, O)}, N = −3 and Ψ* = −(2u_0 + 3u_1)/3. In 30 of them the two light
  bodies are close, and Ψ of that pair stays below Ψ*.
- **Weight data at n = 4.** All 11,025 pairs of binary trees, at two vectors of W_4(32): Ψ* takes 7 values, the largest is 747 at (0, 1, 34, 1156), where the bound is 2,779; the
  relation of Theorem D4 holds at every point found, in all 24 strata.
- **Weight data at n = 5.** All 893,025 pairs of binary trees at three mass vectors, one of them in W_5(50):
  437 points above the search thresholds, none above the bound, the relation holds with N ≠ 0 at each. An
  independent sample of 6.5% of the pairs of trees at a fourth vector: 2,751 points, 24 values of Ψ*, no
  failure.
- **Controls.** With a free scale factor, with equal mass weights and at u = (0, 1, 2, 3) the same searches
  find weight data with N = 0 or with an unbounded Ψ*. So the searches find a failure where there is one.
- **Not tested.** Nothing was computed for n ≥ 6. The balanced cycles of Lemma C start at six bodies. At
  n = 5 the set of weight data is not bounded modulo the rotation (it has rays on which bodies separate or
  one coordinate of one body tends to 0); Proposition D2 is built so that such rays do not matter, and this
  is a place to look for an error.

## 10. For a reader with the repository

Not needed for the sign-off. `docs/allN-direct-route.md` is the working note (§1, §2, §3a; there Lemma A is
§1, Lemma B is Lemma 3 and Lemma C is Lemmas 22, 23 and Steps 1, 2 of Theorem 25 of
`docs/allN-hierarchical-emptiness.md`). `docs/n7-referee-R29.md` is the first referee's report, with its
scripts in `data/n7/allN/hier/r29/`. `scripts/allN/nk_fibre.py` and `scripts/allN/nk_cycle_check.py` are our
search and check programs.

If the reader is an AI session: start with a cleared context; form your verdict from this file before you
open the first referee's report; use your own code for any check; keep local runs under 15 minutes and
4 GB; rent nothing; commit nothing; write your report to `docs/n7-referee-R30.md` and end it with the sheet
of §11.

## 11. The sign-off sheet

For each item answer one of: **holds** / **holds with a fix** (give the fix) / **fails** (give the first
sentence that fails) / **not checked**.

| item | statement to confirm | where |
|---|---|---|
| S1 | If N_n has finitely many solutions modulo the rotation at given positive masses, there are finitely many classes of planar central configurations at those masses; Theorem D5 gives the theorem of §0 | §1 |
| S2 | Lemma A: the cut identities, their terms, the valuations of the terms, the cut condition, also when a position is 0 | §2 |
| S3 | Lemma D0: if the masses with a continuum are Zariski dense, the solution set over K at the masses T^{u*_t} has a component of dimension at least 2 | §3 |
| S4 | Proposition D2: a common upper bound for v(X_tl Y_tl) at all solutions over K excludes a component of dimension at least 2 | §4 |
| S5 | Lemma B | §5 |
| S6 | Lemma C, in particular (C1), the independence of σ(z, w) of the path in (C3), the staircase (a), the levels (b), the corner inequality (c) with its threshold, and the count (d) | §6 |
| S7 | Theorem D4: Step 1 (also with a position equal to 0), Step 2 (the signs, N = 3S_p), Step 3 (the restriction to the bodies), Step 4 (parity and the threshold) | §7 |
| S8 | Theorem D5′ and Theorem D5 follow from S2 to S7 | §8 |
| S9 | No result or example in the literature contradicts Theorem D5 or Theorem D5′; in particular no known continuum lies over masses with hierarchical valuations | §8 |

Three further questions, with free answers.

- Q1. Is the theorem of §0 known for some n ≥ 6, or claimed anywhere? Which of the steps above are already
  in the literature (the argument of §4 is the one we believe is closest to known work)?
- Q2. Does the argument, applied to a system you know to have a continuum at generic parameters, stop at a
  definite step? §8 lists the variants we tried.
- Q3. Overall: **sound** / **sound with fixes** / **not sound** / **cannot say**, and what you would want to
  see before the theorem is announced.
