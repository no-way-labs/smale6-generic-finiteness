# All n: a direct route through N_n over hierarchical masses

*2026-11-16, extended 2026-11-17. Keston Aquino-Michaels with Claude. Not refereed. Status words as in
`docs/allN-status.md`: **proof** / **computation** / **evidence** / **open**. Every computation here uses
floating-point LPs with no certificates, so it is evidence. The tools are those of
`docs/allN-hierarchical-emptiness.md` §8a and §9 (cut generators, the least terms of U), which gave (E_k) and
(C_k) for every k.*

> **2026-11-17.** §3a has a proof, not refereed, of the target theorem for every n (Theorem D5). It has two
> parts. Proposition D2 (§2): N_n is finite at generic masses if no pair of bodies collides on the fibre, that
> is, if every ζ_tl + ω_tl is bounded above there. Theorem D4 (§3a): over W_n(t), t ≥ 2n², the largest value
> Ψ* of Ψ is fixed by the mass weights at every point of the fibre, so it is bounded. The rays found at n = 5
> on 2026-11-16 are separations and single positions that move. They do no harm under Proposition D2.

## 0. The idea in one paragraph

The target theorem for n bodies is that N_n, the normalised system of central configurations in the
coordinates of Albouy and Kaloshin, has finitely many solutions modulo the rotation at generic masses. The
present plan proves it through a census of diagrams (R) and a list of cluster systems (E). This note records
another route with no census. Put weights on the masses, in a hierarchical chamber, and look at the tropical
prevariety of N_n with the cut generators and the torque generators. If its fibre over one mass vector has no
unbounded cell besides the rotation line, then N_n is finite at generic masses. The fibre has this property
at n = 3 and n = 4 (**evidence**). At n = 5 it does not have it with these generators: the far search finds
rays of two kinds at both mass vectors tried (§4). So the hypothesis of Proposition D1 is false at n = 5.
Proposition D2 (2026-11-17) needs less: no pair of bodies collides on the fibre. Theorem D4 proves this
for every n (§3a; **proof, not refereed**).

## 1. The system and its generators

**N_n** (`docs/allN-lemmas-k.md` §6): unknowns X_t, Y_t (t = 0, …, n − 1) and P_tl = P_lt, with

    P_tl² (X_t − X_l)(Y_t − Y_l) = 1,   X_t = Σ_l m_l P_tl³ (X_t − X_l),   Y_t = Σ_l m_l P_tl³ (Y_t − Y_l).

The torus action X ↦ λX, Y ↦ λ⁻¹Y (the rotation) preserves the solutions. A real central configuration with
its conjugate is a solution, so finiteness of the solutions modulo the rotation at generic masses gives the
target theorem for n.

**Coordinates and weights.** Use the coordinates X_t, Y_t, X_tl = X_t − X_l, Y_tl, P_tl. A solution has
X_tl, Y_tl, P_tl ≠ 0; a position X_t or Y_t may vanish, for at most one body per colour. The stratum with no
vanishing position is the main stratum. Weights: ξ_t = v(X_t), η_t = v(Y_t), ζ_tl = v(X_tl), ω_tl = v(Y_tl).
Add a leaf O (the origin) with ζ_tO = ξ_t and ω_tO = η_t. Then ζ and ω are ultrametrics on the n + 1 leaves,
because X_t − X_l − X_tl and the triangle relations have three terms. The rotation shifts ζ by c and ω by −c.

**Generators from the ideal.**
- *Cut generators.* For a set S of bodies, Σ_{t ∈ S} m_t (X-row of t) =
  Σ_{t ∈ S} m_t X_t − Σ_{t ∈ S, l ∉ S} m_t m_l P_tl³ X_tl. A one-body set is the row, and the set of all bodies
  is the centre of mass. The same for Y.
- *Torque generators.* Y_t (X-row of t) − X_t (Y-row of t) = Σ_l m_l P_tl³ (X_l Y_t − X_t Y_l): the positions
  cancel. Summed with the weights m_t over a set S the pairs inside S cancel, and the result is
  Σ_{t ∈ S, l ∉ S} m_t m_l P_tl³ (X_l Y_t − X_t Y_l).

**Values.** With Ψ(t, l) = (ζ_tl + ω_tl)/2 − u_t − u_l for two bodies and Ψ(t, O) = −ξ_t − η_t − u_t, the term of
an edge e of the complete graph on the bodies and O has the value Ψ(e) + ω_e in a cut generator of colour z
and Ψ(e) + ζ_e in colour w, as in §8a of the other note. The values −Ψ are the weights of the terms of
I − U, with I = Σ m_t X_t Y_t and U = Σ m_t m_l P_tl; I − U is in the ideal. A cut of colour z is a partition of
the n + 1 vertices, and its condition is that the largest value over the edges that cross it is attained
twice.

## 2. The reduction (proof, standard facts)

**Proposition D1.** Let u* ∈ R^n have Q-linearly independent coordinates. Suppose that, in every stratum, the
fibre over u* of the tropical prevariety of a finite set of polynomials of the ideal of N_n contains no ray
x + sσ, s ≥ 0, with σ outside the rotation line. Then N_n has finitely many solutions modulo the rotation at
generic masses.

*Proof.* The set of masses with infinitely many solutions modulo the rotation is constructible. If it is
dense, the solution set over an algebraic closure of Q(m) has a component V of dimension at least 2 in one
stratum. Embed Q(m) in the Hahn series field K by m_t ↦ c_t T^{u*_t}, as in Lemma H. The tropicalisation of V
over K is a polyhedral complex of pure dimension dim V (Bieri and Groves), it lies in the fibre of the
prevariety over u*, and a balanced complex of dimension at least 2 has a ray outside any given line. ∎

So bounded cells of any dimension are harmless, and isolated points are harmless. Only unbounded cells
count. A ray x + sσ in the fibre means: σ is a point of the prevariety with trivial weights on the masses
(the classical one, whose rays are the singular diagrams), and x satisfies the conditions restricted to the
terms of largest slope. That is the system of a cell of a diagram, read with mass weights. So the statement
needed is: at hierarchical masses, no initial system of a singular diagram has a tropical solution. The
plan (R) and (E) proves this diagram by diagram. The question of this note is whether the arguments of §8a
prove it for all diagrams at once.

**Proposition D2 (2026-11-17; only one side of each distance counts).** Let u* be as in Proposition D1.
Suppose that, in every stratum and for every pair of bodies {t, l}, the function ζ_tl + ω_tl is bounded above
on the fibre over u*, or bounded below on it. Then N_n has finitely many solutions modulo the rotation at
generic masses.

*Proof.* If not, then as in Proposition D1 the solution set over K has, in one stratum, an irreducible
component V of dimension at least 2. Every point of V is a zero of the polynomials, so its vector of
valuations lies in the fibre. Take a pair {t, l} and the function g = X_tl Y_tl on V. The closure of g(V) is
irreducible, so g is constant on V or g(V) is all of K but finitely many points. In the second case g takes
values of every valuation, and ζ_tl + ω_tl is not bounded on either side on the fibre. So every X_tl Y_tl is a
constant d_tl ≠ 0 on V, and every P_tl is constant on V. The rotation maps V to itself. Fix two bodies a, b.
Every orbit in V has one point with X_ab = 1, so the set V₁ of these points has dimension at least 1. On V₁,
Y_ab = d_ab. For a third body c, X_cb = X_ca + 1 and Y_cb = Y_ca + d_ab, so X_ca Y_ca = d_ca and
(X_ca + 1)(Y_ca + d_ab) = d_cb give Y_ca = d_cb − d_ca − d_ab − d_ab X_ca and a quadratic equation for X_ca
with the leading coefficient −d_ab ≠ 0. So the differences take finitely many values on V₁, and the rows of
N_n give the positions from the differences and the P_tl. So V₁ is finite, a contradiction. ∎

This is the argument of Albouy and Kaloshin that a continuum of central configurations makes a mutual
distance take every value, read on the fibre. It uses no property of a tropical variety: no balancing and
no theorem of Bieri and Groves.

**Corollary D3.** If, in every stratum, no ray of the fibre over u* has a pair of bodies with a positive
slope of ζ_tl + ω_tl (no pair collides along a ray), then N_n is finite at generic masses. The fibre is a
finite union of polyhedra, so a linear function is bounded above on it if and only if its slope is at most 0
on every ray.

So a ray does no harm by itself. A ray on which bodies only separate, or only one position moves, is
allowed. What has to be excluded is a collision.

## 3. What the tools of §8a give (proof)

Let E* be the set of the edges, O-edges included, with the largest Ψ, at a point of the fibre with all cut
conditions.

- **Lemma 19 holds with the same proof**, for the n + 1 vertices: every edge of E* has a partner in E* at its
  ζ-node and at its ω-node. So the graph B on E* has all degrees at least 2 and has a cycle.
- **A cycle of body pairs is excluded over W_n(t), t ≥ n²**: Steps 1 and 2 of Theorem 25 use the cycle and
  Ψ ≤ Ψ* only. A cycle of O-edges gives Σ ± u_t = 0 over distinct bodies and is excluded too.
- So **E* contains an O-edge and a body pair, and every cycle of B is mixed**. At a node where a body pair and
  an O-edge of E* meet, the relation of the cycle does not cancel the height: Ψ has the coefficient 1/2 of
  ζ + ω on body pairs and −1 on O-edges. A mixed cycle fixes heights in terms of the mass weights. Example:
  n = 2, where Ψ(0, 1) = Ψ(1, O) is Kepler's third law.

These statements hold for values in any ordered group, so they hold for the pairs (slope, value) of a ray.
Then: on a ray, the edges of largest slope of Ψ are not all body pairs. A collision of a cluster with no
escape at the same rate is excluded, for every n, by Theorem 25.

**A ray moves some ζ + ω (proof).** Let σ be the direction of a ray, with slopes σζ, σω on the edges. Both
are ultrametric directions: in every triangle the least slope of σζ is attained twice, and the same for σω.
If σζ + σω = 0 on every edge, then −σζ is ultrametric too, so in every triangle σζ takes one value, and σ is
the rotation. So on a ray outside the rotation line some edge has a nonzero slope of ζ + ω.

**The cases of a ray (map; only the first is proved).** Write s_e for the slope of (ζ_e + ω_e)/2 on the edge
e. The slope of Ψ is s_e on a body pair and −2s_tO on an O-edge.
1. *The largest slope of Ψ is positive and attained on body pairs only* (a collision of a cluster faster than
   any escape). Excluded for every n: this is the statement above. **Proof.**
2. *The largest slope of Ψ is positive and attained on an O-edge* (a body escapes, s_tO < 0). **Open.** E*
   then has an O-edge and a body pair, and its cycles are mixed.
3. *The largest slope of Ψ is at most 0 and some body approaches the origin* (s_tO > 0; then no s_tO is
   negative). The system of the largest
   terms is the system of a stratum with that body at the origin. **Open**; the strata have no point at
   n = 3, 4 (§4).
4. *The largest slope of Ψ is 0 and no s_tO moves.* Then some body pair has s_e < 0, because a ray moves
   some ζ + ω. Single bodies or groups turn by
   different complex angles (σζ_tO = c_t, σω_tO = −c_t with c_t not constant). **Open.** At n = 4 these are
   the rays that exist without the torque generators and are removed by them (§4), so a proof has to use the
   torque conditions.

**The cases after Proposition D2 (2026-11-17).** By Corollary D3 a ray does harm only if some body pair has
s_e > 0. Cases 3 and 4 have no such pair, so they do no harm, and the rays found at n = 4 without the torque
generators and at n = 5 (§4) are of these two cases. Cases 1 and 2 are the rays on which Ψ* grows. Theorem D4
below excludes them for every n: Ψ* takes finitely many values on the fibre.

## 3a. Ψ* is fixed by a cycle, and the target theorem (2026-11-17; proof, not refereed)

The edges are the body pairs and the O-edges (t, O). In a stratum with X_s = 0 put ξ_s = +∞, so that
Ψ(s, O) = −∞, and the same for Y_s = 0. Then ζ and ω are ultrametrics with values in R ∪ {+∞}, the leaves s
and O are the two leaves of a node of infinite height, and ζ_sl = ξ_l. Ψ* is the largest value of Ψ over all
edges, E* is the set of the edges that attain it, and B is the graph of Lemma 20 on E*: one vertex for each
node of the tree of ζ and for each node of the tree of ω, both on the n + 1 leaves, and one edge for each
e ∈ E*, between the ζ-node and the ω-node of e. References to Lemmas 3, 19, 20, 22, 23 and Theorem 25 are to
`docs/allN-hierarchical-emptiness.md`.

**Theorem D4.** Let n ≥ 2, t ≥ 2n² and u ∈ W_n(t). At every point of the fibre over u of the prevariety of the
cut generators of N_n, in every stratum, B has a simple cycle, and every simple cycle e_1, …, e_2r of B gives

    N Ψ* + q·u = 0,   N = 3 Σ_{i : e_i a body pair} (−1)^i ≠ 0,
    q = Σ_{i : e_i = (a, b)} 2 (−1)^i (1_a + 1_b) − Σ_{i : e_i = (t, O)} (−1)^i 1_t.

So Ψ* is one of finitely many numbers that depend on u only, and Ψ* ≤ (2n − 1)(|u_0| + … + |u_{n−1}|)/3 on the
fibre.

*Proof.* Fix a point of the fibre.

*Step 1: every vertex of B that meets an edge has degree at least 2.* This is Lemma 19 with the leaf O. The
terms of the cut generator of colour z of a set S of bodies are the edges between S and its complement in
the n + 1 vertices, and the value of the edge e is Ψ(e) + ω_e (§1). Let e ∈ E* with ω-node v, and let S be a
union of children of v that contains one end of e and not the other. One side of this cut is a set of
bodies. A crossing edge (x, y) with x and y in the clade of v has ω_xy = ω_v, and every other crossing edge
has ω_xy < ω_v. So the values of the crossing edges are at most Ψ* + ω_v, with equality if and only if the edge
is in E* and has the ω-node v, and e is such an edge. The cut condition gives a second one. The same holds for the
ζ-node with the colour w. In a stratum with X_s = 0 the term of (s, O) is absent from the generators of colour
z, in agreement with Ψ(s, O) = −∞. It is present in colour w with the value −u_s − η_s, but there s and O lie
in one child of every node other than their own, so (s, O) crosses no cut that the argument uses.

*Step 2: the relation of a cycle.* A finite graph with all degrees at least 2 has a simple cycle
e_1, …, e_2r, r ≥ 1; e_1 and e_2 have the same ω-node, e_2 and e_3 the same ζ-node, and so on. So
Σ_i (−1)^i (ζ_{e_i} + ω_{e_i}) = 0. On E*, ζ_e + ω_e = 2Ψ* + 2u_a + 2u_b for a body pair (a, b) and
ζ_e + ω_e = −Ψ* − u_t for an O-edge (t, O). This gives N′ Ψ* + q·u = 0 with
N′ = 2 Σ_{pairs} (−1)^i − Σ_{O-edges} (−1)^i. The cycle has as many edges at even places as at odd places, so
Σ_{O-edges} (−1)^i = −Σ_{pairs} (−1)^i and N′ = N. The same count gives Σ_j q_j = 5N/3.

*Step 3: a cycle of body pairs does not occur.* Let the cycle have body pairs only. Then N = 0 and
q = 2 Σ_i (−1)^i (1_{a_i} + 1_{b_i}). If q ≠ 0, Lemma 3 excludes q·u = 0 for t ≥ n² (Step 1 of Theorem 25). If
q = 0 the cycle is balanced. Two pairs with the same two nodes do not occur (Lemma 22), so r ≥ 2, and Step 2
of Theorem 25 gives a contradiction for t ≥ n². Lemma 22, Lemma 23 and that step use the pairs of the cycle,
the inequalities Ψ(p, q) ≤ Ψ* for body pairs (p, q), and the clades of the two trees. They hold when the trees
have the extra leaf O: where a clade is searched for its heaviest bodies, O is left out.

*Step 4: N ≠ 0.* By Step 3 the cycle contains an O-edge (t, O). It contains it once, because the cycle is
simple. So q_t is an even number minus (−1)^i, which is odd, and q ≠ 0. If N = 0, then Σ_j q_j = 0 and
|q_j| ≤ 2(n − 1) + 1, so Lemma 3 excludes q·u = 0 for t ≥ (n − 2)(2n − 1) − 1, which is less than 2n². So
N ≠ 0. ∎

The smallest case is n = 2: E* is the pair (0, 1) and the O-edge of the lighter body, with the same two
nodes, N = 3, and Ψ* = −(2u_0 + 3u_1)/3. This is Kepler's third law, P_01³ (m_0 + m_1) = 1.

**Theorem D5 (the target theorem for every n).** For every n ≥ 2, N_n has finitely many solutions modulo the
rotation when the masses lie outside a proper Zariski-closed subset of C^n.

*Proof.* W_n(2n²) is open and not empty, so it contains a vector u* with Q-linearly independent coordinates.
By Theorem D4, in every stratum and for every body pair, (ζ_tl + ω_tl)/2 = Ψ(t, l) + u*_t + u*_l is at most
Ψ* + u*_t + u*_l, which is bounded above on the fibre over u*. Proposition D2 applies. ∎

**What the proof uses.**
- The embedding of Q(m) in the field of Hahn series and the constructible set of bad masses, as in Lemma H
  (`docs/n7-lemma-hierarchical-masses.md`, refereed R5) and in Proposition D1.
- Lemma 3, Lemmas 19, 20, 22, 23 and Step 2 of Theorem 25 (refereed R27 for trees on the bodies; read here
  with the extra leaf O, which no referee has checked).
- The cut generators of both colours. The torque generators are not used.
- No computation, no census of diagrams, no reduction lemma and no cluster system.

**Status.** Written on 2026-11-17 in one session and not refereed. The statement is the target of the whole
project, so it needs a referee before any other document cites it. The checks of §4 agree with Theorem D4 on
every recorded point.

## 4. Computations (evidence; `scripts/allN/nk_fibre.py`)

For each pair of binary trees on the n + 1 leaves the script searches the tie patterns with LPs, as
`fixedu_enum.py` does.

**The test that decides: the far search (`--far R`).** In the gauge that removes the rotation, and for a fixed
generic vector c, the search is restricted to c·x ≥ R and then to c·x ≤ −R. An unbounded cell has points with
|c·x| as large as one likes. So no solution for a large R means that the fibre is bounded modulo the rotation
and has no ray. R must stay below about 10⁵: the tolerance of the tie test is relative, and at R = 9·10⁵ the
search reports false solutions.

| n | mass weights | generators | R | solutions with \|c·x\| ≥ R |
|---|---|---|---|---|
| 3 | (0, 1, 30) | cuts | 3,000 | 0 |
| 3 | (0, 1, 30) | cuts and torque | 3,000 | 0 |
| 4 | (0, 1, 30, 900) | cuts | 9,000 | 22, each on a ray that stays in the prevariety |
| 4 | (0, 1, 30, 900) | cuts and torque | 9,000 and 30,000 | 0 |
| 4 | (0, 1, 2.37, 4.91) | cuts and torque | 100 | 0 |
| 4 | (0, 1, 4.17, 17.3) | cuts and torque | 300 | 0 |
| 5 | (0, 1, 12, 150, 1900) | cuts and torque | 40,000 | 37 (29 distinct points), each on a ray that stays in the prevariety |
| 5 | (0, 1, 2.37, 4.91, 8.53) | cuts and torque | 200 | 20, each on a ray that stays in the prevariety |

So at n = 4 the fibre with the cut and torque generators is bounded modulo the rotation at three mass
vectors, one of them not hierarchical, and N_4 is finite at generic masses by Proposition D1 (as far as float
LPs go). Without the torque generators it has unbounded cells. (Half of the pairs of trees are searched: the
exchange of the two trees exchanges the colours.)

**At n = 5 the fibre with the cut and torque generators is not bounded modulo the rotation** (rental `nk5far`,
all 893,025 pairs of binary trees, 4.2·10⁸ LPs for each mass vector; output in
`data/n7/allN/hier/nk/nk5far_cmp_Znm3GwsGNNWrYtNfimGLsser/`). The far points are of two kinds, the same at
both mass vectors.
- *One coordinate of one body tends to 0.* One ξ_t or one η_t is large and positive, and every other height
  stays bounded. 5 points at the second mass vector (one for each body), 14 at the first. This is an approach
  to the stratum X_t = 0 or Y_t = 0: case 3 of §3 for one coordinate.
- *Two pairs turn in opposite directions about a body at the origin.* One body has ξ and η large and positive.
  Two bodies have ξ large and positive and η large and negative, and the other two the reverse, with ξ_t + η_t
  the same bounded number for the four. The distances inside each pair and to the body at the origin stay
  bounded; the distances between the two pairs tend to infinity. 15 points at each mass vector: 5 choices of
  the body at the origin times 3 splittings of the other four into two pairs. This joins cases 3 and 4 of §3.

Both kinds are present at every choice of bodies, so they do not depend on the mass order. The search does
not say whether a curve of solutions of N_5 lies over these rays: the prevariety of a set of generators
contains the tropical variety and can be larger. The systems of largest terms on the two kinds of rays have
not been examined. (42 and 29 LPs of the two runs ended with a status other than optimal or infeasible; this
can hide a solution and cannot produce one.)

**Checks of Theorem D4 (2026-11-17; evidence).**

*The search above a value of Ψ (`--far-psi R`).* For each edge e the search is restricted to Ψ(e) ≥ R. A
solution is a point of the fibre with Ψ* ≥ R. Control at n = 3, weights (0, 1, 30), where every point has
Ψ* = −1: the search finds points for R = −40, −20 and −1.5, and none for R = −0.9, 0, 10 and 1000.

| n | mass weights | generators | points found with Ψ* ≥ R | bound of Theorem D4 |
|---|---|---|---|---|
| 4 | (0, 1, 30, 900) | cuts | R = 3 and R = 100: 3 points, Ψ* = 569, 1708/3, 579, in leaves with no ray. R = 5000: none | 2172.3 |
| 4 | (0, 1, 30, 900) | cuts and torque | the same 3 points; R = 5000: none | 2172.3 |
| 4 | (0, 1, 2.37, 4.91) | cuts | R = 3, 100, 5000: none (the largest Ψ* found without a threshold is 0.693) | 19.3 |
| 4 | (0, 1, 2.37, 4.91) | cuts and torque | R = 3, 100, 5000: none | 19.3 |

So at n = 4 the fibre with the cut generators alone has rays (22 far solutions in the first table) and no
point with a large Ψ*. Neither vector is in W_4(32); the theorem claims nothing there, and the bound
holds.

*The cycle relation on recorded points (`scripts/allN/nk_cycle_check.py`).* At each point the script builds
E* and B from the recorded heights, checks the degrees, takes a basis of the cycle space of B and evaluates
N Ψ* + q·u on each cycle.

| points | number | a vertex of B of degree 1 | cycles | N Ψ* + q·u ≠ 0 | cycles with N = 0 |
|---|---|---|---|---|---|
| n = 3, (0, 1, 30), cuts and torque | 5 | 0 | 5 | 0 | 0 |
| n = 4, (0, 1, 30, 900), cuts | 58 | 0 | 58 | 0 | 0 |
| n = 4, (0, 1, 2.37, 4.91), cuts | 59 | 0 | 59 | 0 | 0 |
| n = 5, (0, 1, 30, 900, 27000), rental `nk5` | 779 | 0 | 779 | 0 | 0 |
| n = 5, (0, 1, 12, 150, 1900), far points of `nk5far` | 29 | 0 | 29 | 0 | 0 |
| n = 5, (0, 1, 2.37, 4.91, 8.53), far points of `nk5far` | 20 | 0 | 20 | 0 | 0 |

At every one of the 950 points B is a single cycle, E* has an O-edge and a body pair, and N ≠ 0. The values
of Ψ* are the numbers −q·u/N: 38 distinct values at (0, 1, 30, 900, 27000), from −50 to 35379. At the 49
far points of `nk5far` Ψ* lies between −20 and −2/3, every ξ_t + η_t is at least 0, and no ζ_tl + ω_tl is
above 150: the far coordinates are positions that tend to 0 and distances that grow.

Not done: the search above a value of Ψ at n = 5. It needs a rented host: 15 edges in place of the 2 half
spaces of `nk5far`, which cost $0.81 for the two mass vectors together.

**Other outputs of the script, weaker.**
- *Points and dimensions.* Without `--far` the script lists one point for each leaf of the search and the
  dimension of the cell of that point (number of heights minus the rank of the equalities that hold there;
  1 is the rotation line). With cuts and torque: n = 3 at (0, 1, 30): 7 points, all of dimension 1, 3 modulo
  the rotation; n = 4 at (0, 1, 30, 900): 40 points, all of dimension 1, 22 modulo the rotation. These
  dimensions are not a test of boundedness: a leaf contains several cells, and its LP point may lie in a small
  one. At n = 4 without torque every listed point has dimension 1 and 17 leaves contain a ray.
- *Rays of a leaf.* For each solution the script also looks for extreme rays of the polyhedron of its leaf
  and tests whether they stay in the prevariety (verdict 2) or leave it (verdict 1, not conclusive). n = 4 at
  (0, 1, 30, 900): with torque 93 leaves have no ray, 84 have rays that leave, none stays; without torque 17
  stay.
- n = 5 at (0, 1, 30, 900, 27000) with cuts and torque, without `--far` (rental `nk5`, job H): 9,894
  solutions, 779 distinct points, 726 of dimension 1 and 53 of dimension 2. Not conclusive by itself; the far
  search above decides.
- Some isolated points have values of the order of the largest mass weight. Isolated points do no harm,
  whether or not a solution lies over them.
- At (0, 1, 4.17, 17.3) three cells of dimension 2 are listed with the torque generators (the two lightest
  bodies close in ζ, with ζ_23 free). By the far search they are bounded.
- **Strata with a body at the origin** (`--zero-z`, `--zero-w`). With Y_t = 0 for one body t, the search finds
  no point at all at n = 3 (weights (0, 1, 30)) and at n = 4 (weights (0, 1, 30, 900)), for every t. The same
  with X_2 = 0 and Y_3 = 0 at n = 4. This is the forced zero of the roster (relation (a) of G5) for the N type.

## 5. What a proof needs, and what this would replace

*State on 2026-11-16, kept for the record.* A proof through Proposition D1 needed that the fibre has no ray
outside the rotation line, in every stratum. This is false at n = 5 for the cut and torque generators (§4).

*State on 2026-11-17.* Proposition D2 and Theorem D4 give the target theorem for every n (Theorem D5), with
no diagram census, no reduction lemmas and no cluster systems. If the proof stands, gaps G1, G2, G5 and G8 of
the status page are not needed for the target theorem. What it needs now:

1. A referee for §2 (Proposition D2) and §3a (Theorems D4 and D5). The points to press:
   - Lemma 19 with the leaf O, and its form in the strata with a position equal to 0;
   - Step 2 of Theorem 25 for trees with the extra leaf O (Step 3 of Theorem D4);
   - the parity step and the bound on the coefficients of q (Step 4);
   - the passage from a bound on the valuations at the points of V to "X_tl Y_tl is constant on V" in
     Proposition D2, and the count of the solutions with given mutual distances;
   - the generic point: that one mass vector over the field of Hahn series decides generic masses.
2. The search above a value of Ψ at n = 5 (float, rented host), as an independent check of Theorem D4 where
   the fibre is known to have rays.
3. The statement for the paper. Theorem D5 is about N_n at complex masses outside a proper closed set. The
   bad set is not described. Positivity is not used (gap G7 concerns the route through the census).

## 6. Files

| file | content |
|---|---|
| `scripts/allN/nk_fibre.py` | the search; `--torque`, `--sym`, `--far R`, `--far-psi R`, `--zero-z t`, `--zero-w t`, `--out` |
| `scripts/allN/nk_cycle_check.py` | E*, the graph B and the relation N Ψ* + q·u = 0 at the recorded points of an output file |
| `scripts/n7/rhombic_nk.py` | the same on a rented host, one job per mass vector |
