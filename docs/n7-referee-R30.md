# Second independent read of `docs/allN-direct-route-second-read.md`

*Referee R30. An AI session with cleared context, working only from the brief file (the first referee's
report `docs/n7-referee-R29.md` was not opened). Verdict formed from the file; all computations are my own,
written from scratch in a scratch environment (`/tmp/r30env`, numpy 2.5.5 / scipy 1.18.1, HiGHS LP), scripts
in `/tmp/r30/` (not committed). Every individual run was under 15 minutes and 4 GB. Nothing was rented,
nothing committed.*

## Summary

I read §1–§8 line by line and re-derived every valuation, sign, and inequality. **I found no mathematical
error.** I found two cosmetic gaps in the proof as written (threshold constants in (C2) and Step 4 that are
under-justified for small n, and an implicit n ≥ 3 in Proposition D2), neither of which affects any statement.
I then tested the combinatorial core independently and exhaustively where feasible:

- **Lemma C for n ≤ 5: verified exhaustively and exactly**, over *all* ultrametric node structures and *all*
  heights at once (no LP needed): no balanced, (C1)-consistent simple cycle exists.
- **Lemma C for n = 6: verified by exact computation** at a chamber point: exhaustive enumeration of all
  2752² hierarchy pairs leaves exactly 192 candidate hexagon instances (6 abstract types), and all 192 are
  proved height-infeasible by **exact rational Farkas certificates** (not float trust). Float infeasibility
  confirmed at six further chamber vectors; the equal-weight control is feasible for all 192, validating the
  setup.
- **Theorem D4 at n = 4 (with the leaf O): verified exhaustively** over all 236² hierarchy pairs on 5
  vertices, 364,044 distinct LPs: in the chamber, every one of the 25,384 height-realizable E\*-cycles
  satisfies N ≠ 0, NΨ\* + q·u = 0, and Ψ\* ≤ 2779. The value Ψ\* = 747 of §9 is realized. The control
  u = (0,1,2,3) reproduces the note's N = 0 cycle (0,2),(2,O),(0,O),(0,3) with q = ±(1,0,−3,2).
- **n = 7, 8 randomized stress test** (210,000 hierarchy pairs): balanced (C1)-consistent cycles exist
  combinatorially, but none is height-realizable in the chamber.

Transparency note: my *first* LP implementation had a bug (tree-monotonicity direction reversed). It was
caught precisely because the note's own control cycle (§7 remark) came out infeasible; I verified the correct
direction by hand on the note's n = 2 example, fixed it, and re-ran everything. All numbers below are from the
corrected implementation, cross-validated against three independent anchors from the note (n = 2 formula,
§7 control cycle, §9 value 747). The purely combinatorial enumerations never used heights and were unaffected.

Overall verdict (Q3): **sound with fixes** (the fixes are the two cosmetic items below). Given the size of the
claim, I would still want an expert in central configurations to check the literature position before
announcement — see S9/Q1.

## The two fixes

**Fix 1 (threshold constants, (C2) and Step 4).** In (C2) the proof says "Lemma B gives
τ < (n−2)(n−1)−1 < n²". Lemma B gives τ < (Σ_{j<m}|q_j|)/|q_m| − 1, and the crude justified bound is
Σ_{j<m}|q_j| ≤ (n−1)·(n−1) (at most n−1 indices below m, each |q_j| ≤ n−1, |q_m| ≥ 1), i.e.
τ < (n−1)² − 1 = n² − 2n < n². The written constant (n−2)(n−1) is not justified for n ≤ 5 by the argument
given. It *is* justified for n ≥ 6 by the degree sum: Σ_j|q_j| ≤ Σ_j deg_C(j) = 4r and r ≤ n−1 (the cycle has
r distinct ζ-nodes, and a laminar family on n elements has ≤ n−1 clusters), so
Σ_{j<m}|q_j| ≤ 4n−5 ≤ (n−2)(n−1) for n ≥ 6. Either way the conclusion q = 0 for τ ≥ n² is correct.
Same issue in Step 4: the crude bound is τ < (n−1)(2n−1) − 1 = 2n² − 3n < 2n², sufficient for τ ≥ 2n²;
the written (n−2)(2n−1)−1 = 2n²−5n+1 is again only justified for n ≥ 6 (via Σ_j|q_j| ≤ 4·#body-pairs +
#O-edges ≤ 8r−3, r ≤ n). **Minimal fix: replace (n−2) by (n−1) in both displays, or add the degree-sum
sentence.** No statement changes.

**Fix 2 (Proposition D2, n = 2).** The argument fixes two bodies a, b and uses "a third body c". For n = 2
there is no third body; but then on V₁ the positions are already fixed by (N2), (N3) from the constant P and
X_ab = 1, Y_ab = d_ab, so V₁ is a point and the contradiction is immediate. **Minimal fix: one sentence
treating n = 2 separately.** (Theorem D5′ for n = 2 is also immediate from Kepler's third law, §2 example.)

## Item-by-item findings

**S1 (§1).** Holds. Summing the CC equations against m_t gives c = center of mass; λI = U with I, U > 0
gives λ > 0; scaling z ↦ rz sends λ ↦ λ/r³, so r = λ^{1/3} normalizes λ = 1. A normalized CC gives a solution
(X, Y, P) = (z, z̄, 1/|z_tl|); conversely a solution determines z. Same G-orbit ⇒ |λ| = 1 ⇒ rotation (§1
argument correct). Reflections give separate solutions but only coarsen the count, so finiteness mod rotation
implies finiteness mod similarity. The map {CC mod rotation} → {solutions mod G} is injective, so infinitely
many CCs would force infinitely many orbits. Theorem D5 ⇒ theorem of §0; a proper Q-closed subset of C^n
meets R^n in a proper real algebraic set (a nonzero Q-polynomial is nonzero over R), measure zero.

**S2 (Lemma A, §2).** Holds. I re-derived: v(m_t m_l P³ X_tl) = u_t + u_l − (3/2)(ζ+ω) + ζ = −(Ψ+ω) ✓;
v(m_t X_t) = u_t + ξ_t = −Φ^z(t,O) ✓; Φ^z(t,O) = Ψ(t,O) + η_t when Y_t ≠ 0 ✓. The cut identity is (N2)
multiplied by m_t and summed, internal pairs cancel by antisymmetry ✓. Terms are elements of K summing to 0,
so the least valuation among nonzero terms is attained twice ✓ (ultrametric). Zero terms: body-pair terms
never zero (F1); O-edge term m_t X_t zero iff X_t = 0, correctly excluded; the definition of Φ^z(t,O) when
X_t ≠ 0 but Y_t = 0 is still −u_t − ξ_t, correct. The tree facts T1–T4 each follow from one triangle
inequality, including +∞ heights (I checked T2 and T4 with infinite values). The n = 2 example checks out
symbolically: Ψ(0,1) = Ψ(1,O) = −(2u_0+3u_1)/3, Ψ(0,O) smaller by u_1−u_0, cycle N = −3, q = (−2,−3);
my LP reproduces Ψ\* = −2 at u = (0,2) exactly.

**S3 (Lemma D0, §3).** Holds. (i) G = G_m connected ⇒ preserves each irreducible component; free action ⇒
orbits dim 1; a dim-1 component is one orbit (orbits constructible of full dimension ⇒ contain dense opens ⇒
two meet ⇒ equal); finitely many components (Noetherian) ⇒ finitely many orbits iff all components dim ≤ 1.
(ii) The fiber-dimension locus {x : dim_x X_{f(x)} ≥ 2} is closed (upper semicontinuity of fiber dimension,
EGA IV 13.1.3) and defined over Q; image constructible (Chevalley). (iii) A constructible set in no proper
closed subset contains a dense open, hence the generic point; a point of 𝒳₂ over the generic point gives a
component of dim ≥ 2 over Q(m)‾. (iv) Q-linear independence of u\* makes distinct monomials map to distinct
exponents, so Q(m) ↪ K; the embedding extends to Q(m)‾ since K is algebraically closed (Zorn); geometric
irreducibility and dimension are preserved under algebraically closed base change; the K-fiber at T^{u\*} is
the base change of the generic fiber. All standard and correct. K = Q̄((T^R)) is algebraically closed
(maximally complete, divisible value group, algebraically closed residue field, char 0) ✓.

**S4 (Proposition D2, §4).** Holds (with Fix 2 for n = 2). g = X_tl Y_tl regular on irreducible V: image
constructible in A¹, so constant or cofinite; cofinite ⇒ elements of valuation > M (K has all real
valuations) ⇒ excluded ⇒ g constant d ≠ 0. P² = 1/d: two values, V irreducible ⇒ P constant. The slice
V₁ = {X_ab = 1} satisfies V ≅ G × V₁ (free action with global regular slice), dim V₁ = dim V − 1 ≥ 1.
The quadratic −d_ab X_ca² + (d_cb − d_ca − d_ab)X_ca − d_ca = 0 re-derives correctly from
X_ca Y_ca = d_ca and (X_ca+1)(Y_ca+d_ab) = d_cb; leading coefficient d_ab ≠ 0 ⇒ ≤ 2 values; all differences
and then positions (N2), (N3) finitely valued ⇒ V₁ finite, contradiction. This is indeed the valuation form
of the Albouy–Kaloshin "continuum forces a collision" argument, and it correctly also excludes rays where
bodies only separate or one coordinate tends to 0 (those make some X_tl Y_tl take every value).

**S5 (Lemma B, §5).** Holds. q·u = Σ_{j≥1} q_j(u_j−u_0); m = 1 immediate; m ≥ 2:
|q_m|(u_m−u_0) ≤ Σ_{j<m}|q_j|(u_{m−1}−u_0) and u_m−u_0 > (1+τ)(u_{m−1}−u_0) > 0 give
(1+τ)|q_m| < Σ_{j<m}|q_j|. Contrapositive as stated. Chamber nonempty open cone ✓.

**S6 (Lemma C, §6).** Holds with Fix 1. Line-by-line:
- (C1): a ∈ Z_e∩W_e ⇒ ζ_ca ≥ ζ_cd, ω_ca ≥ ω_cd ⇒ Ψ° ≥ Ψ(c,a) ≥ Ψ° + u_d − u_a ⇒ u_a ≥ u_d, symmetrically
  u_a ≥ u_c; distinct weights ⇒ a strictly lighter than both endpoints; two pairs with the same node pair
  would both be "the two heaviest" ⇒ equal ⇒ no multi-edges in E°, r ≥ 2. ✓
- (C2): telescoping of shared heights gives Σ(−1)^i(ζ+ω) = 0; on E° this is 2q·u (even cycle kills Ψ°);
  q integer, sum 0, |q_j| ≤ n−1; Lemma B with τ ≥ n² forces q = 0 (Fix 1 for the constant). ✓
- (C3): h_z + g_w − 2Ψ° = 2σ(z,w)·u by telescoping along an odd path; I verified the path-independence
  sign claim explicitly on a hexagon: with ζ-nodes between e_{even}, e_{odd}, the two path vectors satisfy
  σ₂ − σ₁ = q = 0. Coefficient sum 2 ✓.
- (C4): p,p′ ∈ Z∩W ⇒ ζ_pp′ ≥ h_z, ω_pp′ ≥ g_w ⇒ (1_p+1_p′−σ)·u ≥ 0 ✓.
- (C5)(a): nodes containing L form chains (T3); Z_j ⊆ Z_i and W_j ⊆ W_i would put x_j in Z_i∩W_i, lighter
  than L by (C1), contradicting L lightest on the cycle; hence opposite strict staircase ✓.
- (b): ℓ exists because total change = q_L = 0; range ≤ m/2 (m/2 up-steps, m/2 down); σ_L = ℓ(z)−ℓ(w)
  verified with the parity convention (f_i = e_{s+i−1}, s odd, so parity(f_i) = parity(i)). ✓
- (c): Z_i∩W_j ∋ L, x_i, x_j with x_i, x_j heavier than L ⇒ top two p,p′ heavier than L; v = 1_p+1_p′−σ
  has sum 0, |v_k| ≤ n, support in indices ≤ L, v_L = −(ℓ(z_i)−ℓ(w_j)); L ≥ 2 as a name; if ℓ(z_i)−ℓ(w_j) ≥ 1
  then v·u < (−(1+τ) + n(n−2))(u_{L−1}−u_0) ≤ 0 for τ ≥ n²−2n−1, contradicting (C4). Every step checked,
  including u_L−u_0 > (1+τ)(u_{L−1}−u_0) and Σ_{k<L}|v_k| ≤ (L−1)n ≤ (n−2)n. ✓
- (d): ℓ(w_j) ≥ ℓ(z_i) = ℓ(w_i)+1 for i < j ⇒ ℓ(z_m) ≥ ℓ(w_1)+m ⇒ range ≥ m > m/2, against (b). ✓

  Computational confirmation (my own code, exact where stated):
  - n ≤ 5: enumerated all hierarchies (laminar families; 4, 26, 236 for n = 3,4,5 — every ultrametric node
    structure, ties included via multifurcation). For all pairs, enumerated all simple cycles of the full
    bipartite graph G_full (B° is a subgraph), kept balanced ones, applied the (C1) filter with the chamber
    order. Result: n = 3: 0 balanced; n = 4: 96 balanced, 0 pass C1; n = 5: 39,840 balanced, 0 pass C1.
    Since every B° cycle in the chamber is balanced (C2) and passes C1, **Lemma C for n ≤ 5 holds for all
    heights and all chamber u, exhaustively**. (Balanced 4-cycles do exist in G_full — e.g.
    (0,1),(0,2),(2,5),(1,5) — and are killed by C1 exactly as the proof says; the note's remark "none for
    n ≤ 5" is correct for cycles that could lie in E°.)
  - n = 6: all 2752² = 7,573,504 hierarchy pairs (with a proved necessary pre-filter on the lightest cycle
    body). Exactly **192 survivor instances**: 6 abstract hexagon edge-sets × 32 realizations, all hexagons
    on all six bodies, each body of degree 2. (The note's "96" matches up to counting convention: 192 ordered
    pair instances = 96 unordered, or 96 (hexagon, parity-class) pairs.) The six edge-sets are, up to the
    relabeling symmetry, the ones containing (3,5),(4,5) and two edges at 0; explicit list in `/tmp/r30`).
  - For each survivor, LP over cluster heights + Ψ° with Ψ(e) = Ψ° on the hexagon, Ψ(f) ≤ Ψ° elsewhere,
    h(child) ≥ h(parent) (eps = 0, the strong form: any true counterexample merges equal heights into a
    coarser hierarchy, also enumerated, with strict gaps there). At u = (0,1,39,1483,56355,2141491) ∈ W_6(36):
    **all 192 infeasible, each certified by an exact rational Farkas certificate** (y ≥ 0,
    A_ubᵀy + A_eqᵀz = 0, b_ub·y + b_eq·z = −1, verified in Fraction arithmetic; support-based rational
    Gaussian elimination). Also infeasible (float HiGHS) at τ = 37 and five random chamber vectors.
    Control u = 0: all 192 feasible, with the cycle edges genuinely at max Ψ — the setup finds realizations
    when they exist. u = (0,1,2,3,4,5) and u = 2^j: infeasible (the chamber threshold is not sharp; harmless).
  - n = 7 (150,000 random pairs) and n = 8 (60,000): 15 and 12 balanced C1-consistent cycles found
    combinatorially, **0 height-feasible in the chamber**.

**S7 (Theorem D4, §7).** Holds with Fix 1 (Step 4 constant).
- Step 1: e ∈ E\* has real Ψ, so for an O-edge both X_t, Y_t ≠ 0 and its term is nonzero in both colours;
  body-pair terms never zero. v = ω-node of e, real height; S′ a union of children separating the ends of e;
  S the O-free side, nonempty. Crossing terms: body pairs nonzero; O-edge (r,O) with Y_r = 0 cannot cross
  (ω_rO = +∞ > ω_v forces r, O into one child or both outside, by T2); O-edge with X_r = 0 is a zero term,
  ignored. Nonzero crossing f = (x,y): y ∈ v ⇒ different children ⇒ ω_f = ω_v (T1); y ∉ v ⇒ ω_f < ω_v (T2);
  so Φ^z(f) ≤ Ψ\* + ω_v with equality iff f ∈ E\* and ω-node(f) = v (T4). e attains it; cut condition gives a
  second ⇒ degree ≥ 2. Colour w symmetric. All cases checked, including positions equal to 0. ✓
- Step 2: telescoping ✓; ζ+ω = 2Ψ\*+2u_a+2u_b (body pair), −Ψ\*−u_t (O-edge) ✓; (2S_p−S_O)Ψ\* + q·u = 0,
  S_p+S_O = 0 ⇒ N = 3S_p ✓; Σq_j = 4S_p−S_O = 5N/3 ✓.
- Step 3: restriction to bodies is an ultrametric; Ψ° = Ψ\* (attained by a body pair); full ζ-node ∩ bodies
  = restricted node; two body pairs have equal full nodes iff equal restricted nodes (both directions
  checked via T3/T4 and "a node containing a pair contains the pair's node"); so a body-only simple cycle of
  B maps to a simple cycle of B°, excluded by Lemma C (τ ≥ 2n² ≥ n²). ✓
- Step 4: (t,O) once ⇒ q_t odd ⇒ q ≠ 0; N = 0 ⇒ Σq = 0; |q_j| ≤ 2n−1; Lemma B contradicts τ ≥ 2n²
  (Fix 1 constant). Bound |Ψ\*| ≤ (2n−1)Σ|u_j|/3 from |N| ≥ 3 ✓; finitely many (N,q) ✓.
- Computational confirmation, n = 4 with O (5 vertices), exhaustive over all 236² hierarchy pairs,
  364,044 distinct (pair, edge-set) LPs, **all cyclic orders checked for N, q** (the relation is
  order-dependent; feasibility is order-free):
  - Chamber u = (0,1,34,1156) ∈ W_4(32): 25,384 feasible E\*-cycles; **0 with N = 0, 0 relation violations,
    0 bound violations** (bound 2779, matching §9). 25 distinct Ψ\* values in my superset (I do not impose
    the cut conditions, so more than the note's 7 weight-data values — consistent); **Ψ\* = 747 is realized**
    (216 instances), matching §9's largest weight-data value; my superset maximum is 747.333 = 2242/3
    (q = (−3,−2,−2,2), N = −3), presumably cut-condition-inadmissible.
  - Control u = (0,1,2,3): 608 N = 0 cases, **including the note's exact cycle (0,2),(2,O),(0,O),(0,3)
    with q = ±(1,0,−3,2)** (432 instances), reproducing the §7 remark. 0 relation/bound violations.
  - The "B has a simple cycle" half of Step 1 uses the cut conditions and was checked manually only; my LP
    superset does not test it (it is a statement about weight data, not arbitrary heights).

**S8 (§8).** Holds. D5′: Lemma A ⇒ weight datum; D4 ⇒ Ψ\* ≤ M_0; every body pair an edge ⇒
ζ_tl+ω_tl ≤ 2M_0+2u_t+2u_l ≤ M = 2M_0+4max|u|; D2 ⇒ no component dim ≥ 2; D0(i) over K ⇒ finitely many
orbits. D5: W_n(2n²) open nonempty ⇒ contains Q-linearly independent u\*; if bad masses were in no proper
closed set, D0 gives a dim ≥ 2 component over K at T^{u\*}, against D5′; the bad set is Q-constructible
(D0(ii)), closure proper Q-closed. The §8 "where each hypothesis enters" table checks out, including the
free-λ variant: an O-edge term λX_t adds −v(λ) to Ψ(t,O), hence −S_O·v(λ) = (N/3)v(λ) to the relation,
exactly as stated.

**S9 (literature).** Holds to the best of my knowledge, with an honesty caveat: **I did not perform a live
literature search** (no search tool in this session); this is from training knowledge.
- No published proof of generic planar finiteness for n ≥ 6 is known to me; the brief's premise matches my
  knowledge. n = 4: Hampton–Moeckel (2006) for all positive masses, Albouy–Kaloshin (2012) alternative.
  n = 5: Albouy–Kaloshin obtained finiteness under explicit conditions/partial results; I am not certain of
  the current status of generic positive-mass finiteness at n = 5 (the brief's float checks at n = 5 are
  consistent with either).
- Known continua of planar relative equilibria all sit at **fixed mass ratios** (a continuum is, by
  definition, at fixed masses): Roberts' five-body continuum (one negative mass; the brief gives
  (1,1,1,1,−1/4); I cannot verify the exact ratio from memory, but the argument is ratio-independent).
  A fixed nonzero mass vector has a fixed valuation vector up to shift, so its tropicalization is the
  diagonal line R(1,…,1), which meets no permuted chamber W_n(τ) (the chamber requires strictly increasing,
  super-geometric gaps). Hence no known continuum lies over hierarchical valuations, and none contradicts
  D5′. Continua with zero masses (restricted problems) are outside (K\*)^n; spatial continua are irrelevant.
  A positive-mass continuum at special fixed masses, if one were found, would *not* contradict the theorem
  (the bad set is allowed to be nonempty); only a continuum at hierarchical valuations, or a Zariski-dense
  family of bad masses, would.
- I know no family contradicting any statement of §8.

## The three free questions

**Q1.** Known/claimed: n = 3 classical (Euler, Lagrange); n = 4 all positive masses (Hampton–Moeckel 2006;
Albouy–Kaloshin 2012); n = 5 partial/conditional (Albouy–Kaloshin); n ≥ 6 nothing published that I know of.
Closest steps in the literature: the coordinates (X,Y,P) and the whole "continuum ⇒ some mutual distance
collides at unbounded order ⇒ finiteness" strategy are Albouy–Kaloshin's (their singular sequences and
circled diagrams); §4 is a clean valuation-only repackaging of that idea, and the brief says so. The cut
identities are classical momentum/Dziobek-type identities. The Hahn-series specialization (D0) is the
standard tropical/tropical-compactness move (Payne-type statements are invoked correctly as a remark).
What I do not recognize from the literature is the chamber W_n(τ) + Lemma B + Lemma C package, i.e. the
exclusion of *all* balanced cycles under strong hierarchy, and the resulting all-n generic statement. If
correct, that is the new content. **Caveat: an expert should confirm none of this is already in the
Albouy–Kaloshin five-body work or in the tropical-CC literature, which I cannot search.**

**Q2.** Yes — the argument stops exactly where it should on the variants I could test:
- Free scale λ: Step 2 acquires (N/3)v(λ) (algebra verified), Ψ\* is unbounded, and the system genuinely has
  a continuum (the extra scaling dimension). The O-edges are precisely what pins the scale.
- Equal mass weights: Lemma B is inapplicable; body-pair cycles exist. My equal-u control realizes all 192
  n = 6 hexagons as E°-cycles.
- u = (0,1,2,3): N = 0 cycles exist; I reproduced the note's exact example with q = ±(1,0,−3,2), q·u = 0.
- "Every pair interacts" is used exactly in the last line of D5′ (every body pair is an edge of E\*'s
  competition); dropping an interaction removes the bound on that pair's ζ+ω.

**Q3.** **Sound with fixes.** The fixes are Fix 1 (two threshold constants; one-line replacements) and Fix 2
(one sentence for n = 2 in D2). I found no substantive error in §1–§8, and the combinatorial core passed
exhaustive independent verification at n ≤ 6 (exact at n ≤ 5 and, via rational Farkas certificates, at n = 6
for a chamber point) plus randomized checks at n = 7, 8. Before the theorem is announced I would want:
1. the two fixes applied;
2. a referee who knows the central-configuration literature to confirm S9/Q1 by an actual search
   (especially the n = 5 status and any overlap of Lemma C with known diagram classifications);
3. the exact n = 6 certificates (or an equivalent published verification) included as supplementary
   material, since Lemma C is the load-bearing step for n ≥ 6 and is untestable by solution-counting;
4. ideally a second independent human read of (C3)–(C5) and D0(ii)–(iv), the two places where a subtle
   sign or a scheme-theoretic point could hide. My checks make me confident, but a claim of this size
   deserves more than one AI referee and one context-free referee.

## Reproducibility of my checks

Scripts (not committed): `/tmp/r30/check_cycles.py` (hierarchies, node maps, simple-cycle enumerator),
`check2.py` (n ≤ 5 exhaustive balance+C1), `check6fast.py` (n = 6 exhaustive with proved pre-filter),
`lp6.py` (n = 6 height LPs + controls), `cert6.py`/`cert6b.py` (exact rational Farkas certificates),
`d4n4.py`/`d4n4b.py` (D4 n = 4 with O, all orders), `n7rand.py` (n = 7, 8 randomized). Environment:
`/tmp/r30env` (numpy 2.5.5, scipy 1.18.1, HiGHS). Key parameters: chamber vectors
u = (0,1,39,1483,56355,2141491) (n = 6, τ = 36), u = (0,1,34,1156) (n = 4, τ = 32); controls u = 0 and
u = (0,1,2,3) (n = 4), u = (0,1,2,3,4,5), u = 2^j (n = 6). LP monotonicity: h(child) ≥ h(parent) + eps,
eps = 0 for the strong infeasibility statement. The cycle enumerator and the balance/C1 filters are exact
integer/set computations; only the LP feasibility calls are floating point, and the n = 6 chamber
infeasibility is additionally certified exactly over Q.

## §11 sign-off sheet

| item | verdict | note |
|---|---|---|
| S1 | **holds** | normalization, orbit↔rotation, reflection coarsening, Q-closed ⇒ measure zero: all checked |
| S2 | **holds** | valuations, cut condition, zero-term cases, T1–T4 with +∞: checked; n = 2 example exact |
| S3 | **holds** | semicontinuity, Chevalley, generic-point fiber, Hahn embedding, geometric irreducibility: checked |
| S4 | **holds** | with Fix 2 (n = 2 sentence); cofinite-image, slice, quadratic: checked |
| S5 | **holds** | re-derived; used in all computations |
| S6 | **holds with a fix** | Fix 1: replace (n−2) by (n−1) in the (C2) threshold display (or add degree-sum justification); all steps (C1)–(C5) verified by hand; exhaustive exact verification n ≤ 5; n = 6: 192/192 exact rational Farkas certificates at a chamber point; controls pass |
| S7 | **holds with a fix** | Fix 1 same in Step 4 (crude 2n²−3n < 2n² suffices); Steps 1–4 checked by hand incl. zero positions; exhaustive n = 4 with O: 25,384 feasible cycles, 0 violations; note's control cycle and Ψ\* = 747 reproduced |
| S8 | **holds** | D5′ and D5 re-derived from S2–S7; free-λ term (N/3)v(λ) verified |
| S9 | **holds** | no known contradiction; Roberts-type continua at fixed ratios ⇒ diagonal tropicalization, miss all chambers; caveat: training knowledge, not a live search; n = 5 literature status uncertain |

**Q3 overall: sound with fixes.**
