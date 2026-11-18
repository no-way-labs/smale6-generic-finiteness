# R29. The direct route: Proposition D2, Theorem D4, Theorem D5 (`docs/allN-direct-route.md` §1, §2, §3a)

*2026-11-17. Adversarial read of `docs/allN-direct-route.md` at commit **bbc262f**: §1 (the system N_n, the
coordinates, the weights, the cut generators, the values Ψ), §2 (Proposition D1, Proposition D2, Corollary D3),
§3a (Theorem D4, Theorem D5, "What the proof uses"), and the statements of §4 that concern Theorem D4 and the
strata. Sources read for the definitions and the lemmas: `docs/allN-hierarchical-emptiness.md` §1, §2 (Lemma 3)
and §8a (Lemmas 17 to 23, Theorem 25), `docs/allN-lemmas-k.md` §6, `docs/n7-lemma-hierarchical-masses.md` §1
(Lemma H), `docs/allN-status.md` §0 items 16 to 19, and `docs/n7-referee-R28.md`. I did not read
`docs/n7-referee-R27.md`; I read Lemmas 19, 22, 23 and Steps 1 and 2 of Theorem 25 line by line myself (§5).
The referee is a session with a cleared context. Scripts and outputs are in `data/n7/allN/hier/r29/` (called
`r29/` below). None of them imports `scripts/allN/nk_fibre.py`, `fixedu_enum.py` or `nk_cycle_check.py`, and
none imports code of an earlier referee round; the search loop of `r29_lp.py` follows the design of
`r28/r28_lp.py`, which I read. `nk_fibre.py` was read, and run as a program for comparison (§10).*

## Verdict

**Sound with fixes.** I found no error in Proposition D2, Theorem D4 or Theorem D5. Every step holds as
written or with one sentence added, and the attempts of §9 to make the argument prove a false statement all
stop at a named step. The fixes are three: the reduction to a component of dimension at least 2 is asserted
and not written out (issue 1), Step 3 of Theorem D4 is easier to check through the restriction to the bodies
(issue 2), and one sentence of §4 about the strata is false for the cut generators alone, because of a wrong
test in `nk_fibre.py` (issue 3). None of them changes a statement of §2 or §3a.

What this verdict rests on: one referee, one day, a line-by-line read, exact algebra for the generators, all
114 solutions of N_3 at four mass vectors, and float LP searches for n ≤ 5. Balanced cycles of body pairs
start at six bodies, so the part of the proof that carries Theorem 25 is tested by no computation of mine. The
statement is new and large. It should have a second read by a person who knows the literature on central
configurations before it is cited (§9, last paragraph, says where I would look for a counterexample).

## What I checked and what held

### 1. §1: the generators and the values

`r29/r29_cutgen.py`, exact, n = 2, 3, 4, 5. Polynomials are dictionaries over the variables m_t, X_t, Y_t, P_tl.

- For every nonempty set S of bodies and both colours, Σ_{t ∈ S} m_t (row of t) equals
  Σ_{t ∈ S} m_t X_t − Σ_{t ∈ S, l ∉ S} m_t m_l P_tl³ (X_t − X_l) as polynomials. Counts (both colours): 6, 14, 30,
  62 generators with 12, 48, 160, 480 terms.
- The terms are one for each edge between S and its complement in the n + 1 vertices (bodies and O). Every
  partition of the n + 1 vertices into two nonempty sides has exactly one side without O. That side is a
  nonempty set of bodies, and its generator has exactly the crossing edges. So each of the 2^n − 1 partitions
  (3, 7, 15, 31) has one generator. The set of all bodies gives the centre of mass, whose edges are the n
  O-edges.
- At 200 random weight points for each n (two random ultrametrics on the n + 1 leaves with merged nodes
  allowed, random u, rationals), the term of the edge e has the value Ψ(e) + ω_e in colour z and Ψ(e) + ζ_e
  in colour w, computed from the exponents of its monomial: 2,400, 9,600, 32,000 and 96,000 values, no
  failure.
- Σ_t m_t Y_t (X-row of t) = Σ_t m_t X_t Y_t − Σ_{t<l} m_t m_l P_tl³ X_tl Y_tl, so I − U is in the ideal. The
  torque identity of §1 holds with the sign of the note.
- ζ and ω are ultrametrics on the n + 1 leaves: X_t − X_l − X_tl = 0 and X_tl + X_ls + X_st = 0 have three terms.
- The conditions are stated for a prevariety. For a solution over K they hold for a simpler reason, which
  the proof of D2 needs: the terms of a generator are elements of K with the valuations above and their sum
  is 0, so the least valuation is attained twice. No statement about distinct monomials is needed.
- Strata. A solution has X_tl, Y_tl, P_tl ≠ 0, so at most one X_t and at most one Y_t vanish. With X_s = 0
  the term of (s, O) is absent in colour z. With Y_s = 0 the term of (s, O) is present in colour z with the
  value −u_s − ξ_s, and Ψ(s, O) = −∞. So "the value is Ψ(e) + ω_e" fails for exactly this term (and for its
  mirror in colour w). §4 checks that the proof never uses it.

### 2. All solutions of N_2 and N_3 at numerically hierarchical masses

**N_2.** X_0 − X_1 = (m_0 + m_1) P³ (X_0 − X_1), so P³ (m_0 + m_1) = 1. With u_0 < u_1: ζ_01 + ω_01 = 2u_0/3,
ξ_1 = ζ_01, ξ_0 = ζ_01 + u_1 − u_0, the same for η. Then Ψ(0, 1) = Ψ(1, O) = −(2u_0 + 3u_1)/3 and
Ψ(0, O) is smaller by u_1 − u_0. This is the example after Theorem D4. A stratum has no solution: X_0 = 0
contradicts X_0 = m_1 P³ X_01.

**N_3, derivation.** Put D_tl = X_l Y_t − X_t Y_l. The centre of mass in both colours gives
m_2 D_02 = −m_1 D_01. The torque of body 0 is m_1 P_01³ D_01 + m_2 P_02³ D_02 = 0, so
D_01 (P_01³ − P_02³) = 0, and the same for the other bodies. So either all P_tl³ are equal (type L), or all
D_tl = 0 (type C).
- Type L: the rows give P_tl³ = 1/M, M = m_0 + m_1 + m_2. So P_tl = M^(−1/3) ρ^j with ρ a cube root of 1: 27
  choices. With X_01 = 1 and d_tl = P_tl^(−2): Y_01 = d_01, and X_12 = x solves
  d_01 x² + (d_01 + d_12 − d_02) x + d_12 = 0. 54 solutions modulo the rotation.
- Type C: the vectors (X_t, Y_t) lie on one line through 0, and a rotation gives X_t = Y_t = x_t. Then
  P_tl = s_tl/(x_t − x_l) with s_tl = ±1, and s_01 = 1 modulo the rotation by −1. With p = x_0 − x_1 and
  x_1 − x_2 = τp the rows give a quintic for τ and p³ as a function of τ. 4 · 5 · 3 = 60 solutions.

**N_3, computation.** `r29/r29_n3sol.py`, mpmath. Masses m_t = c_t ε^(u_t). The valuation of a coordinate x is
−log|x|/log(1/ε), rounded to a multiple of 1/6. All 114 solutions are computed, checked in the nine equations,
and then tested with the same code as the LP points (`r29_common.py`: ultrametrics, the 14 cut conditions
from the monomials, E*, B, all simple cycles, N and q).

| c | u | in W_3(18) | ε | digits | largest residual | largest distance to a multiple of 1/6 | failures | Ψ* at all 114 |
|---|---|---|---|---|---|---|---|---|
| (2, 3, 5) | (0, 1, 20) | yes | 10⁻⁶⁰ | 3,800 | 1.3·10⁻³⁷⁷¹ | 0.0096 | none | −1 |
| (2, −3, 5) | (0, 1, 25) | yes | 10⁻⁴⁰ | 3,200 | 2.6·10⁻³¹⁸¹ | 0.0144 | none | −1 |
| (1, 1, 1) | (0, 3, 70) | yes | 10⁻¹⁵ | 3,350 | 5.9·10⁻³³²⁹ | 0.0250 | none | −3 |
| (7, 2, 3) | (0, 1, 2) | no | 10⁻⁴⁰ | 440 | 2.7·10⁻⁴²¹ | 0.0235 | none | −1 |

- At every solution E* = {(0, 1), (1, O)}, B is one cycle with these two edges, N = −3 and q = (−2, −3, 0). So
  Ψ* = −(2u_0 + 3u_1)/3, the value of Theorem D4, and it is the value of N_2 for the two heavy bodies.
- No solution has a position equal to 0.
- The two light bodies come close in 30 of the 60 solutions of type C: ζ_12 + ω_12 = 2u_1/3 in 18 of them and
  u_1 in 12, against 0 in the other 84. Then Ψ(1, 2) ≤ u_1/2 − u_1 − u_2 stays below Ψ*. So the test has
  solutions with a close pair, and the bound holds on them.
- The first run with u = (0, 3, 70) rounded to multiples of 1/3 and reported 12 failures. The valuations are
  half-integers there (X_12 has valuation 3/2), so the grid was wrong. With multiples of 1/6 there is no
  failure. `n3sol_c.out` is the second run.

### 3. Proposition D1, Proposition D2, Corollary D3

**The reduction to a component of dimension at least 2 (first sentences of both proofs).** True; the note
asserts it in one sentence. What it needs is in issue 1. I checked:
- The solution set of N_n at a mass vector is a closed subset of an affine space. The rotation group is a
  connected group that acts freely, because X_ab ≠ 0. So every irreducible component is invariant and has
  dimension at least 1. A component of dimension 1 is one orbit: two orbits in it are both dense and
  constructible, so they meet. So "finitely many solutions modulo the rotation" is "no component of dimension
  at least 2". This is the right negation.
- The set of masses with a component of dimension at least 2 is the image of a closed set (the points where
  the local dimension of the fibre is at least 2; Chevalley), so it is constructible, and it is defined over
  Q. If it lies in no proper closed subset, it contains the generic point of the mass space. The fibre over
  the generic point, over an algebraic closure of Q(m), then has a component of dimension at least 2.
- The embedding Q(m) → K, m_t ↦ c_t T^(u*_t), is that of Lemma H: it needs c_t ≠ 0 and Q-linearly independent
  u*_t, nothing else. K is algebraically closed, so a component over the closure of Q(m) stays irreducible of
  the same dimension over K. The solution set of N_n over K at the masses c_t T^(u*_t) is this base change.

**Proposition D2, line by line.**
- *The valuation vector of a K-point of V is a point of the fibre.* Yes, by the remark of §1 above: at a
  K-point the cut identities hold exactly. The point lies in the stratum given by its vanishing positions.
  V is a component in one stratum, but a K-point of V with a large valuation of g may lie in a smaller
  stratum. The hypothesis is made for every stratum, and Theorem D4 is proved for every stratum, so nothing
  is lost (issue 5 asks for the sentence).
- *g is constant or g(V) misses finitely many points.* V is irreducible, g is a regular function, the image
  of V is a constructible subset of the line with an irreducible closure. So it is a point or the complement
  of a finite set. K is algebraically closed, so this is a statement about K-points. The value group of K is
  R and every valuation is taken by infinitely many elements, so a set that misses finitely many points
  contains elements of every valuation. So ζ_tl + ω_tl is not bounded on either side on the valuations of the
  K-points of V. The proof needs the bound of the hypothesis on these points only.
- *P_tl is constant.* P_tl² = 1/d_tl has two solutions and V is irreducible.
- *The rotation maps V to itself.* The group is connected.
- *V₁.* Every orbit meets X_ab = 1 in one point, so dim V₁ ≥ dim V − 1 ≥ 1.
- *The quadratic.* X_cb = X_ca + 1 and Y_cb = Y_ca + d_ab. From X_ca Y_ca = d_ca and (X_ca + 1)(Y_ca + d_ab) = d_cb:
  Y_ca = d_cb − d_ca − d_ab − d_ab X_ca, and then −d_ab X_ca² + (d_cb − d_ca − d_ab) X_ca − d_ca = 0. The leading
  coefficient is not 0. So X_ca and Y_ca take at most two values for each c, all differences take finitely
  many values on V₁, and the rows give the positions. For n = 2 there is no third body and the same
  conclusion holds. A position equal to 0 changes nothing here.
- So the proposition holds. It can be said shorter: by the hypothesis P_tl² = 1/(X_tl Y_tl) has valuation
  bounded below on V, and a regular function on an irreducible variety whose values have bounded valuation
  is constant.

**Proposition D1.** Holds, with the facts it cites: the tropicalisation of V in the torus of its stratum has
pure dimension dim V, and its recession fan has the same dimension, so it has rays outside any line. Theorem
D5 does not use D1. Its hypothesis is false at n = 5 (§4 of the note).

**Corollary D3.** Holds: a linear function is bounded above on a finite union of polyhedra if and only if it
is at most 0 on every recession direction.

### 4. Theorem D4, Step 1 (Lemma 19 with the leaf O)

Read with e a body pair and with e an O-edge, in the main stratum and in the strata.

- Let e ∈ E*, v its ω-node, S a union of children of v with one end of e inside and the other outside. Ψ(e)
  is finite, so ω_e = ω_v is finite. One of S and its complement has no O; the generator of that side has
  the edges between S and its complement (§1). A crossing edge inside the clade of v has ω = ω_v, a crossing
  edge that leaves the clade has ω < ω_v. So every crossing value is at most Ψ* + ω_v, with equality exactly
  on the edges of E* with the ω-node v. The edge e attains it, and the cut condition gives a second edge.
  The same for the ζ-node with colour w. This is the proof of the note, and it is right.
- e an O-edge (t, O): the same lines. S can be the set of all bodies (when O alone is a child of v); the
  generator is then the centre of mass.
- Stratum X_s = 0. In colour z the term of (s, O) is absent; every other crossing term has its value, so
  the argument for the ω-nodes is unchanged. In colour w the term of (s, O) has the value −u_s − η_s, which
  is not bounded by Ψ* + ζ_v. It does not cross a cut of the argument: the cut is a union of children of the
  ζ-node v of an edge of E*; v is not the node {s, O}, because the only edge with that node is (s, O) and
  Ψ(s, O) = −∞; and s and O lie in one child of every other node, or outside its clade. The note gives the
  second half of this reason.
- Stratum Y_r = 0: the mirror statement. Both X_s = 0 and Y_r = 0, with r = s or r ≠ s: the two arguments
  concern different colours and do not interact.
- So every vertex of B that meets an edge has degree at least 2, in every stratum.

Tests: at every point of §2 and §7 to §8 (456 solutions of N_3; 15 to 2,751 LP points per run, strata
included) no vertex of B has degree 1.

### 5. Theorem D4, Steps 2, 3 and 4

**Step 2.** In a simple cycle e_1, …, e_2r of the bipartite graph B consecutive edges share an ω-node and a
ζ-node in turn, so Σ (−1)^i ω_{e_i} = 0 and Σ (−1)^i ζ_{e_i} = 0. On E*, ζ_e + ω_e = 2Ψ* + 2u_a + 2u_b for a pair
and −Ψ* − u_t for an O-edge. With S_p = Σ_{pairs} (−1)^i and S_O = Σ_{O-edges} (−1)^i: S_p + S_O = 0,
N′ = 2S_p − S_O = 3S_p = N, and Σ_j q_j = 4S_p − S_O = 5S_p = 5N/3. The signs of q are as stated. Check on
n = 2: N = −3, q = (−2, −3) for the cycle (0, 1), (1, O) (`lp2.out` and by hand).

**Step 3.** A cycle of body pairs only has N = 0 and q with even entries, |q_j| ≤ 2(n − 1), sum 0. If q ≠ 0,
Lemma 3 gives t(q) ≤ (n − 2)(n − 1) − 1. If q = 0, the note cites Lemma 22, Lemma 23 and Step 2 of Theorem 25
"with O left out". I checked this in two ways.
- Directly. Lemma 22 uses ζ_ca ≥ ζ_cd and ω_ca ≥ ω_cd for a body a in both clades and Ψ(c, a) ≤ Ψ*. Lemma 23
  uses the heights of the nodes of the cycle and Ψ(p, q) ≤ Ψ* for two bodies p, q in Z ∩ W. Step 2 (a) to (d)
  uses the chains of the clades that contain L, Lemma 22, Lemma 23 (P) at Z_i ∩ W_j for the two heaviest
  bodies of that set, and a count. In each place only bodies are named, the heights are those of nodes of
  body pairs (finite), and Ψ* is the largest value over all edges, so Ψ(p, q) ≤ Ψ* holds for body pairs. A
  leaf O in a clade changes nothing.
- By restriction (issue 2). Let ζ′, ω′ be the restrictions of ζ, ω to the bodies. The clade of the node of a
  body pair e in the tree of ζ′ is the clade of its node in the tree of ζ without O. Two body pairs have the
  same ζ-node if and only if they have the same ζ′-node: if the clades agree on the bodies, each clade
  contains the other pair, and a node is the least clade of its pair. A cycle of body pairs in E* makes
  Ψ* the largest value over the body pairs. So the cycle is a simple cycle of the graph B of (ζ′, ω′, u),
  inside its top pairs. Steps 1 and 2 of Theorem 25 say that this graph has no cycle over W_n(t), t ≥ n²;
  they are statements about two ultrametrics on the bodies and u (R28, §2). So Step 3 is Theorem 25 for the
  restriction, word for word.
- I read Step 2 of Theorem 25 again: the function p exists because the cycle is balanced at L; its
  coefficient claim telescopes; max p − min p ≤ m/2; the corner form v has sum 0, is 0 above L, has
  v_L = −(p(z_i) − p(w_j)), and is negative in W_k(t) for t ≥ k² − 2k − 1 if v_L ≤ −1; the count gives
  max p − min p ≥ m. I found nothing wrong.
- Lemma 22 for r = 1 is not needed: two distinct pairs with the same two nodes give q ≠ 0.
- The cycle must be simple in Step 3 (Lemma 23 takes a path of the cycle) and in Step 4.

**Step 4.** A simple cycle uses each edge of B once, and (t, O) is one edge. So an O-edge of the cycle
occurs once, q_t is even ± 1, and q ≠ 0. If N = 0 then Σ q_j = 0, |q_j| ≤ 2(n − 1) + 1, and Lemma 3 applies:
its hypotheses are q ≠ 0, coefficient sum 0, and the bodies named by increasing mass weight, which is the
convention of W_n(t). t(q) ≤ (n − 2)(2n − 1) − 1 = 2n² − 5n + 1. So N ≠ 0 over W_n(2n²). The thresholds the
proof uses are n² − 2n − 1 (Step 3) and 2n² − 5n + 1 (Step 4).

That Step 4 does real work is seen at u = (0, 1, 2, 3) (§9 (c)): there a cycle through two O-edges has N = 0.

**The conclusion.** Ψ* = −q·u/N with |N| ≥ 3 and |q_j| ≤ 2n − 1, so the bound of the theorem holds, and N, q
range over finite sets.

### 6. Theorem D5

- W_n(2n²) is an open cone and not empty, so it contains a vector with Q-linearly independent coordinates.
- Theorem D4 bounds Ψ* above on the fibre over u*, in every stratum; (ζ_tl + ω_tl)/2 = Ψ(t, l) + u*_t + u*_l is
  at most Ψ* + u*_t + u*_l for every body pair, because every body pair is an edge. This is the side of the
  inequality that D2 accepts ("bounded above").
- The fibre of D2 is the fibre of D4: the cut conditions and the two ultrametrics, in each stratum.
- What the proof gives is more than the statement. For every mass vector in (K*)^n whose valuations lie in
  W_n(2n²), whatever the leading coefficients, N_n has finitely many solutions over K modulo the rotation.
  The Q-linear independence is used only to embed Q(m). So the tropicalisation of the closure of the bad set
  (in the torus of the masses) misses W_n(2n²) and its images under the permutations of the bodies. A known
  continuum over a family of masses with a tropical point in W_n(2n²) would refute the theorem (§9).

### 7. LP searches of the fibre, without any lemma of the note

`r29/r29_lp.py`. For a pair of binary trees (a child at least as high as its parent, so every pair of
ultrametrics is covered) the unknowns are the heights. The conditions are the 2 (2^n − 1) cut conditions. The
search branches on the two terms that tie on top of the first condition that fails at the LP point. Three
modes: `list` (one point for each leaf of the search), `far` (the extra row Ψ(e) ≥ R, for each edge e), `max`
(branch and bound for the largest Ψ(e) subject to Ψ(e) ≥ Ψ(e′) for all e′; the largest result is the largest
Ψ* on the fibre; a cap of 10⁴ (1 + range of u) keeps the LPs bounded). Every point found is tested again from
the monomials: ultrametrics, all cut conditions, E*, B, degrees, all simple cycles, N, q, the relation,
Lemma 22. Float LPs (HiGHS), no certificates. An LP with a status other than optimal or infeasible is solved
again from a cold start; none stayed undecided in any run.

Main stratum:

| n | u | in W_n(2n²) | mode | pairs of trees | LPs | points | failures of D4 | values of Ψ* |
|---|---|---|---|---|---|---|---|---|
| 3 | (0, 1, 20), (0, 1, 50), (−3, −2, 17), (0, 0.3, 7), (0, 1, 20.37) | yes | list | 225 each | 5,044 to 5,212 | 15 to 19 | 0 | one value, −(2u_0 + 3u_1)/3 |
| 3 | the same five | yes | max | 225 each | about 15,800 | | 0 | the same value is the largest |
| 4 | (0, 1, 34, 1156) | yes | list | 11,025 | 1,278,749 | 576 | 0 | −34.67, −34, −1, −0.667, 735.67, 736, 747 |
| 4 | (0, 1, 34, 1156) | yes | max | 11,025 | 4,442,016 | | 0 | largest 747; bound of D4: 2,779 |
| 4 | (0, 1, 34, 1156) | yes | far | 11,025 | 4.7 to 5.0 million each | R = 748, 2,780, 100,000: 0. R = 746.5: 8, all with Ψ* = 747 | 0 | |
| 4 | (0, 2, 70, 2500) | yes | list, max | 11,025 | 1,278,750; 4,442,655 | 576 | 0 | −71.33, −70, −2, −1.33, 1594.67, 1595.33, 1618; bound 6,001 |
| 5 | (0, 1, 52, 2704, 140608) | yes | list | 2,996 (sample, seed 29) | 1,462,681 | 116 | 0 | 7 values, largest 93,686 |
| 5 | (0, 1, 52, 2704, 140608) | yes | list | 57,917 (sample, seed 30; 6.5% of 893,025) | 29,209,006 | 2,751 | 0 | 24 values from −2,738.67 to 184,738; bound 430,095 |

- At every point B is a single cycle with an O-edge and a body pair, N ≠ 0, and N Ψ* + q·u = 0 to the float
  precision.
- The largest value at n = 4 is the relation of the cycle (0, 2), (2, 3), (1, 2), (1, O): N = −3,
  q = (−2, −3, −2, 2), Ψ* = (2u_3 − 2u_2 − 3u_1 − 2u_0)/3 = 747. At this point ζ_03 = 3,058, ζ_02 = ζ_23 = 2,310,
  ω_13 = 2,312. So the fibre has points with collisions of very high order, and their order is fixed by u.
  This is what the theorem says.
- The `list` mode gives one point per leaf of the search, so it does not list all cells. A point of a cell
  on which Ψ* is not constant would violate the relation at that point, and the `max` mode does not depend
  on the list.

Vectors outside W_n(2n²) (mode `max`; the theorem claims nothing there):

| n | u | result |
|---|---|---|
| 3 | (0, 1, 1.01), (0, 1, 1.5), (0, 1, 2), (0, 1, 2.37), (0, 1, 3), (0, 1, 10) | no failure; largest Ψ* = −1 |
| 4 | (0, 1, 30, 900) | no failure; the three largest values are 569, 569.33, 579, as in §4 of the note |
| 4 | (0, 1, 2.37, 4.91) | no failure; largest 0.6933, as in §4 of the note |
| 4 | (0, 1, 4, 16) | no failure; largest 7 |
| 4 | (0, 1, 2, 3) | **cycles with N = 0, Ψ* reaches the cap** (§9 (c)) |
| 3, 4 | two equal weights, or all equal | **cycles with N = 0, Ψ* reaches the cap** (§9 (b)) |
| 4 | (0, 0, 0, 0), mode `far`, R = 100,000 | 81,558 points: the mode `far` finds points above a threshold when there are some |

### 8. The strata

`r29_lp.py --zs s` (X_s = 0: the tree of ζ is a tree on the bodies, ξ_t = ζ_ts, no term of (s, O) in colour
z) and `--ws r`. Modes `list` and `max` in each stratum.

| n | u | strata | runs, LPs | result |
|---|---|---|---|---|
| 2 | (0, 1) | all 8 | 8 runs, 0 LPs (`lp2.out`) | no point: in every stratum a cut has one term |
| 3 | (0, 1, 20), (0, 1, 50) | X_s = 0; Y_r = 0; both (15 strata) | 60 runs, 36,456 LPs | no point |
| 3 | (0, 0, 0), (0, 1, 1) | X_s = 0 | 6 runs (`lp3stratactl.out`) | control: points found (45, 45, 45 and 27, 0, 0 for s = 0, 1, 2), so the search finds points in a stratum when there are some |
| 4 | (0, 1, 34, 1156) | X_s = 0 or Y_s = 0, one body | 16 runs | **points**: 7, 7, 2, 3 for s = 0, 1, 2, 3 in each colour; largest Ψ* = −1, −2/3, −1, −1 |
| 4 | (0, 1, 34, 1156) | X_s = 0 and Y_r = 0 | 32 runs | **points** for r = s = 0 (2) and r = s = 1 (2); none in the other 14 |
| 4 | all 24 strata together | | 48 runs, 5,375,087 LPs | no failure of a statement of Theorem D4 at any point |

So at n = 4 the strata of the fibre of the cut generators are not empty, and Theorem D4 is tested there:
every point has a single cycle with N = −3 and the relation holds. Example (u = (0, 1, 30, 900), Y_0 = 0,
`lp4strata_u30.out`): ξ = (928, 29, 0, 928), ζ_01 = ζ_13 = 29, ζ_03 = 928, ζ_02 = ζ_12 = ζ_23 = 0; η_1 = −29,
η_2 = 0, η_3 = −928, ω_0l = η_l, ω_12 = −29, ω_13 = ω_23 = −928. I checked all 30 cut conditions of this point
by hand. E* = {(0, 1), (1, O)} and Ψ* = −1. The note says that these strata have no point (issue 3).

### 9. Does the argument prove too much?

I applied the proof to systems and mass vectors where the conclusion is false or not claimed, and looked
for the step that stops it.

- **(a) A free scale factor, λ X_t = Σ …, λ Y_t = Σ ….** Through each solution of this system there is a
  one-parameter family modulo the rotation: X, Y ↦ sX, sY, P ↦ P/s, λ ↦ λ/s³. With ℓ = v(λ) the O-edges have Ψ(t, O) = −ξ_t − η_t − u_t − ℓ. Steps 1, 3 and 4 go through. Step 2
  gives N Ψ* + q·u + (N/3) ℓ = 0, so Ψ* is not bounded, and D2 does not apply. The normalisation enters the
  proof through the O-edges, and N ≠ 0 says that every cycle sees it. LP control (`r29_lp.py --freescale`,
  `scale.out`): at u = (0, 1), (0, 1, 20) and (0, 1, 34, 1156) the largest Ψ(e) reaches the cap of the
  search (20,000, 210,000, 1.157·10⁷). So the `max` search reports an unbounded Ψ* when there is one, at the
  same mass weights where it reports 747 for N_4.
- **(b) Masses that are not hierarchical: equal weights.** At u = (0, 0, 0), (0, 0, 1), (0, 1, 1) and
  (0, 0, 0, 0) the search finds cycles with N = 0 (cycles of body pairs, and of O-edges) and Ψ* reaches the
  cap. Lemma 3 is not available, and Steps 3 and 4 stop. Roberts' continuum for five bodies has the masses
  (1, 1, 1, 1, −1/4), with the weights (0, 0, 0, 0, 0). The bad set contains the line through this vector
  (N_n is homogeneous: m ↦ sm, P ↦ s^(−1/3) P, X, Y ↦ s^(1/3) X, Y), and the tropicalisation of that line is
  R (1, …, 1), outside the open cone W_5(50). So this example does not contradict the stronger statement of
  §6.
- **(c) Distinct weights outside the chamber.** At u = (0, 1, 2, 3) the search finds the cycle
  (0, 2), (2, O), (0, O), (0, 3) with N = 0 and q = (1, 0, −3, 2), q·u = 0, and Ψ* reaches the cap, with
  ω_02 = ω_03 = 80,004: bodies 0, 2, 3 collide in the colour w. t(q) = 1/2, so Lemma 3 excludes this relation
  in W_4(t) for t ≥ 1/2. This is a mixed cycle of the kind that Step 4 excludes, and it shows that the
  theorem is false without a hypothesis on u. At the other vectors with distinct weights that I tried the
  conclusion holds (§7).
- **(d) Two groups of bodies that do not attract each other.** Replace m_t m_l by 0 for t in one group and l
  in the other. Each group can be rotated by its own λ, so there is a continuum for all masses. The cut
  generators have no term for a pair across the groups. Theorem D4 still bounds Ψ on the edges that have
  terms, but the last line of the proof of Theorem D5 needs Ψ(t, l) ≤ Ψ* for every body pair, and a pair
  across the groups is not an edge. So the proof stops at "for every body pair". In N_n every pair is an
  edge of every cut that separates it.
- **(e) Variants where the proof goes through unchanged.** Constants κ_t ≠ 0 of weight 0 on the left sides
  (κ_t X_t = Σ …) and symmetric coupling constants c_tl ≠ 0 of weight 0 in place of 1: the term values are
  the same, so Theorem D4 and Proposition D2 hold word for word. I know no continuum at generic masses in
  these families.
- **(f) Another exponent a in place of 3 (P_tl^a).** Then Ψ(t, l) = (a − 2)(ζ_tl + ω_tl)/2 − u_t − u_l, and the
  relation of a cycle is (a/(a − 2)) S_p Ψ* + q·u = 0, where q has the coefficient 2/(a − 2) on the body
  pairs and 1 on the O-edges. For a = 2 (vortices) Ψ of a pair does not contain the heights, and for a = 0
  the coefficient of Ψ* is 0: the proof stops. The parity argument of Step 4 is special to a = 3: it needs
  2k/(a − 2) ≠ ±1 for integers k, which fails for a = 4, 6, …. I did not pursue this.

A person who knows the literature should look for a counterexample in two places: a family of masses with a
known continuum and a tropical point in a hierarchical chamber (§6), and the variants of (e). I found none.

### 10. The author's program (comparison)

`r29/author_scripts.out`.
- `nk_fibre.py 4 0,1,34,1156 --far-psi 746.5`: 8 solutions, all with largest Ψ = 747. `--far-psi 748`: none.
  This agrees with my search (§7).
- My `max` search at (0, 1, 30, 900) and (0, 1, 2.37, 4.91) gives the values that §4 of the note records
  (569, 1708/3, 579; 0.693).
- `nk_fibre.py 4 0,1,30,900 --zero-w t`, without `--torque`: 7, 7, 3, 10 solutions for t = 0, 1, 2, 3. With
  `--torque`: 0 for every t. See issue 3.

## Issues

1. **fix. The reduction to a component of dimension at least 2 is asserted, not written.** Where: proof of
   Proposition D1, sentences 1 and 2, and "as in Proposition D1" in the proof of Proposition D2. The
   statement is true (§3). Add: (i) the rotation group is connected and acts freely on the solutions, so
   every component of the solution set is invariant, and a component of dimension 1 is one orbit; so
   infinitely many solutions modulo the rotation means a component of dimension at least 2; (ii) the set of
   masses with such a component is constructible and defined over Q (upper semicontinuity of the dimension
   of the fibre, Chevalley); (iii) if it is not in a proper closed subset it contains the generic point, as
   in step 1 of Lemma H; (iv) a component over the closure of Q(m) stays irreducible of the same dimension
   over K. The paper needs these four sentences, because Theorem D5 rests on them and Lemma H states them
   for "has a solution", not for "has a component of dimension 2".
2. **fix. Step 3 of Theorem D4: use the restriction to the bodies.** Where: "Lemma 22, Lemma 23 and that step
   use … They hold when the trees have the extra leaf O: where a clade is searched for its heaviest bodies,
   O is left out." The sentence is true (§5), but it asks the reader to read three proofs again with a new
   leaf. Replace it by: restrict ζ and ω to the bodies; a cycle of body pairs of B is a cycle of the graph B
   of the restriction, inside its top pairs (the two-line argument of §5); Steps 1 and 2 of Theorem 25 are
   statements about two ultrametrics on the bodies and u ∈ W_n(t), t ≥ n², and exclude it. Then the part of
   the proof that R27 refereed applies with no change, and Lemma 22 for r = 1 need not be cited.
3. **fix. §4, "Strata with a body at the origin": false for the cut generators alone; a wrong test in
   `scripts/allN/nk_fibre.py`.** Where: the bullet "With Y_t = 0 for one body t, the search finds no point at
   all … at n = 4 (weights (0, 1, 30, 900)), for every t."
   - With the cut and torque generators the author's program finds no point. With the cut generators alone,
     which are the generators of Theorem D4, the strata have points: my search finds 7, 7, 2, 3 at
     (0, 1, 30, 900) and at (0, 1, 34, 1156) (§8, with an example checked by hand), and the author's program
     without `--torque` finds 7, 7, 3, 10.
   - The author's counts for t = 2, 3 contain points that are not in the stratum. `nk_fibre.py` l. 177 skips
     a tree only if another body l has lca(l, t) equal to the node n0 of (t, O). It accepts a tree in which
     that node contains other bodies below it. Example: the ω-tree ((((0, 3), 2), O), 1) with t = 3. The node
     of (3, O) is {0, 2, 3, O}, the bodies 0 and 2 meet 3 at lower nodes, and the tree is searched with the
     height of {0, 2, 3, O} set to that of its parent plus 1 and the position term of body 3 dropped. The run
     `--zero-w 3` lists a point from this tree with largest Ψ = 579 and ω_03 = 4,178 ≠ η_0 = 1,801. In the
     stratum ω_03 = η_0. The right test: the node of (t, O) has the two leaves t and O only.
   - The results "no point" with `--torque` stand, because the trees of the stratum are among the trees
     searched. The counts and the largest Ψ without `--torque` are wrong for t = 2, 3.
   - Repair: correct the test, and say in the bullet that the strata are empty with the cut and torque
     generators and not empty with the cut generators alone at n = 4. Theorem D4 covers them and holds at
     every point found there (§8). The proof of Theorem D5 does not use this bullet.
4. **wording. Step 1 in the strata.** Where: "there s and O lie in one child of every node other than their
   own, so (s, O) crosses no cut that the argument uses." Add: their own node is not the node of an edge of
   E*, because its only edge is (s, O) and Ψ(s, O) = −∞. Add that the stratum Y_r = 0 is the mirror case, and
   that the two cases concern different colours, so they hold together (r = s or r ≠ s). In §1, "the term of
   an edge e … has the value Ψ(e) + ω_e" holds in the main stratum; say so there.
5. **wording. Proof of Proposition D2.** (i) V is a component in one stratum, and a point of V with a large
   valuation of g may lie in a smaller stratum; the hypothesis covers every stratum. (ii) "every P_tl is
   constant on V" uses that V is irreducible. (iii) "The rotation maps V to itself" uses that the group is
   connected. (iv) State the fibre: the valuations that satisfy the cut conditions and the two ultrametric
   conditions, in the stratum of the point.
6. **wording. Definitions.** W_n(t) is not defined in the note, and not in §1 of
   `docs/allN-hierarchical-emptiness.md`, to which §3a sends the reader; the definition is in
   `docs/allN-hierarchical-chambers.md` l. 38. Give it in §3a, with the convention that the bodies are named
   by increasing mass weight (a larger u is a lighter body). In Theorem D4 the letter t is the parameter of
   the chamber and a body ("(t, O)").
7. **wording. "Ψ* is fixed by the mass weights".** Where: the note of 2026-11-17 at the top and the title of
   §3a. Ψ* takes finitely many values that depend on u: 7 at n = 4, at least 24 at n = 5 (§7). The statement
   of Theorem D4 says this correctly. Also: the proof uses t ≥ 2n² − 5n + 1; this can be said in one bracket.
8. **wording. Theorem D5, what it gives.** Say that the closed set is defined over Q and is not described,
   that a class of planar central configurations modulo similarity is one orbit of solutions (the scale is
   fixed by the rows, the centre of mass by the sum of the rows), so the theorem gives finitely many classes
   for positive masses outside a proper algebraic subset. Say also what the proof gives over K (§6), because
   it is the form in which a counterexample can be looked for.

## Not checked

- The LP searches are float and have no certificates. "No point above R" and the largest values of Ψ* are
  evidence.
- n = 5 is a sample of 6.5% of the ordered pairs of trees at one mass vector, in the mode `list` only. The
  modes `max` and `far` were not run at n = 5, and no stratum was searched at n = 5. Nothing was run for
  n ≥ 6.
- Balanced cycles of body pairs start at six bodies. So no computation of mine exercises the case q = 0 of
  Step 3 (Step 2 of Theorem 25). For it I rely on my reading (§5) and on the checks of R27, which I did not
  read.
- Actual solutions were computed for n = 2 and n = 3 only. For n = 4 I have points of the prevariety, not
  solutions. The valuations of the solutions of N_3 are read off at one small ε per run, with an error up to
  0.025.
- The facts cited and not reproved: Chevalley's theorem and the semicontinuity of the dimension of a fibre;
  that K is algebraically closed; for Proposition D1, the theorem of Bieri and Groves and the dimension of
  the recession fan. Lemma H was read for the embedding only.
- I did not search the literature. I cannot certify that no known continuum contradicts the statement of §6;
  I tried Roberts' family and the variants of §9.
- §3 (the cases of a ray), §4 beyond the statements named above, and `scripts/allN/nk_cycle_check.py` were
  not refereed.

## Files (`data/n7/allN/hier/r29/`)

PY is a Python with numpy and highspy. PYLIB is a directory with mpmath 1.4.1 (installed outside the repo
with `pip install --target`). All LP runs used 4 processes. The longest run is the second sample at n = 5
(741 s). All LP runs together took about 55 minutes of wall time on 4 processes. Each run of `r29_n3sol.py`
took under 3 minutes on one process.

| file | what | command |
|---|---|---|
| `r29_common.py` | binary trees, Ψ, term values from the monomials, cut conditions, E*, B, simple cycles, N, q | imported |
| `r29_cutgen.py`, `cutgen.out` | the cut generators expanded from the rows, n = 2 to 5 | `PY r29_cutgen.py` |
| `r29_n3sol.py`, `n3sol_a.out` to `n3sol_d.out` | all 114 solutions of N_3 at four mass vectors | `PY r29_n3sol.py PYLIB --c c0,c1,c2 --u u0,u1,u2 --E e` |
| `r29_lp.py` | the search of the fibre: `--mode list\|far\|max`, `--zs`, `--ws`, `--sample`, `--freescale` | `PY r29_lp.py N --u … --mode …` |
| `r29_batch.py` | the batches | `PY r29_batch.py n2\|n3\|n3strata\|n3ctl\|n3stratactl\|n4\|n4strata\|n4ctl\|n4far\|scale`; `PY r29_batch.py n5 NPAIRS SEED` |
| `lp2.out` | n = 2: the main stratum and the 8 strata | batch `n2` |
| `lp3.out`, `lp3strata.out`, `lp3ctl.out`, `lp3stratactl.out` | n = 3: five vectors of W_3(18); 15 strata at two of them; nine vectors outside; the control of the search in a stratum | batches `n3`, `n3strata`, `n3ctl`, `n3stratactl` |
| `lp4.out`, `lp4far.out`, `lp4ctl.out` | n = 4: two vectors of W_4(32); the thresholds R; five vectors outside | batches `n4`, `n4far`, `n4ctl` |
| `lp4strata.out`, `lp4strata_u30.out` | n = 4: 24 strata at (0, 1, 34, 1156); Y_t = 0 at (0, 1, 30, 900) | batch `n4strata`; `PY r29_lp.py 4 --u 0,1,30,900 --ws t --mode list` |
| `lp5.out`, `lp5b.out` | n = 5, samples with seeds 29 and 30 | `PY r29_batch.py n5 3000 29`, `PY r29_batch.py n5 60000 30` |
| `scale.out` | the control with a free scale factor | batch `scale` |
| `author_scripts.out` | runs of `scripts/allN/nk_fibre.py` | see the file |

The first runs of the batches `n3` and `n3ctl` had 2 LPs with the status "unknown" in the mode `max`. I added
the second solve from a cold start and ran them again; the files are the second runs, with no LP undecided.
