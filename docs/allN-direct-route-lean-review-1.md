freeze as is

I found no harmful difference or counterexample. The weight datum and chamber hypotheses can hold together for every $n\ge2$. The existing tests leave that combination untested above two bodies.

## Definitions and statements

The first column gives lines in Challenge.lean. The second gives the corresponding sentence or formula in the brief.

| Lean declaration | Brief | Assessment | Reason |
| --- | --- | --- | --- |
| `Chamber`, 24–25 | §5, 244–246. For $\tau\ge0$, $u_1>u_0$ and the $j$-th gap exceeds $\tau(u_{j-1}-u_0)$ for $2\le j<n$. | differs, harmless | The inequalities agree. The raw predicate also accepts negative $\tau$ and padded inputs at $n<2$. |
| `lemmaB`, 28–32 | §5, 252–253. A nonzero zero-sum $q$ with last nonzero index $m$ has $q\cdot u\ne0$ under the stated chamber and ratio bound. | differs, harmless | The statement uses the prefix through $m$, which represents $q$ with a zero tail. |
| `IsUltra`, 38–40 | §2, 99–106. The least of the three triangle values is attained at least twice, with diagonal $+\infty$ by convention. | differs, harmless | Symmetry and all distinct-triple inequalities give the triangle rule. Raw diagonal entries are ignored. |
| `node`, 43–44 | §2, 105–107. $N(x,y)=\{p:d_{xp}\ge d_{xy}\}$ and contains both endpoints. | faithful | The filter includes $x$ directly and uses $d_{xy}\le d_{xp}$ elsewhere. |
| `IsCycle`, 49–59 | §6, 267–269. A simple cycle uses $2r$ distinct edges and $2r$ distinct vertices, alternating the two colours of adjacency. | faithful | The fields impose exactly those requirements, including $r=1$. |
| `psiPair`, 64 | §2, 118–120. $\Psi(a,b)=(\zeta_{ab}+\omega_{ab})/2-u_a-u_b$. | faithful | The average and both subtractions agree. |
| `topPairs`, 67–68 | §6, 262–263. $E^\circ$ is the set of body pairs attaining the largest $\Psi$. | faithful | Each ordered representative must dominate every body pair. |
| `lemmaC`, 71–75 | §6, 261–271. For two body ultrametrics and $u\in W_n(\tau)$ with $\tau\ge n^2$, $B^\circ$ has no simple cycle. | faithful | The maximum is taken on body pairs and the negation excludes every simple cycle. |
| `Datum`, 80–86 | §2, 152–156. A weight datum has a mass vector, real body-pair heights, and O-edge heights in $\mathbb R\cup\{+\infty\}$ in two colours. | faithful | The structure stores those inputs. `IsWeightDatum` supplies their conditions. |
| `Datum.dz`, 93–94 | §2, 99–106. $\zeta_{tO}=\xi_t$ and the diagonal convention is $+\infty$. | differs, harmless | Both orders of the O-edge agree and $\zeta_{OO}=+\infty$. Body diagonal entries are padding. |
| `Datum.dw`, 97–98 | §2, 99–106. $\omega_{tO}=\eta_t$ with the same diagonal convention. | differs, harmless | Both orders of the O-edge agree and $\omega_{OO}=+\infty$. Body diagonal entries are padding. |
| `Datum.psiO`, 101 | §2, 120. $\Psi(t,O)=-\xi_t-\eta_t-u_t$, with value $-\infty$ when either position is zero. | differs, harmless | It computes the real branch. `IsEdge` excludes the infinite branch. |
| `Datum.psiE`, 104 | §2, 118–120. $\Psi$ has one formula on body pairs and another on O-edges. | differs, harmless | It dispatches to the two formulas on edges with real $\Psi$. |
| `Datum.IsEdge`, 107–108 | §2, 102–103 and 118–127. Every distinct pair is an edge, with $\Psi=-\infty$ allowed on an O-edge. | differs, harmless | Lean's predicate keeps the finite-$\Psi$ subset. It contains every body pair. |
| `Datum.IsPsiStar`, 111 | §2, 125–127. $\Psi^*$ is the largest edge value and is real. | faithful | It requires an attained upper bound. Discarding $-\infty$ preserves that maximum. |
| `Datum.Estar`, 114 | §2, 125. $E^*$ is the set of edges with $\Psi(e)=\Psi^*$. | faithful | It keeps exactly the admitted edges with value $P$. |
| `Datum.phiZ`, 118–119 | §2, 138–140. $\Phi^z=\Psi+\omega$ on body pairs and $-u_t-\xi_t$ on nonzero O terms. | faithful | The real formulas use the opposite height for body pairs and the own-colour height at O. |
| `Datum.phiW`, 122–123 | §2, 144. $\Phi^w=\Psi+\zeta$ on body pairs and $-u_t-\eta_t$ on nonzero O terms. | faithful | It applies the colour swap. |
| `Datum.termsZ`, 127–128 | §2, 132–140. Count the crossing body pairs and the O terms with $X_t\ne0$. | faithful | It orients the pair from $S$ and checks only $\xi_t$ for an O term. |
| `Datum.termsW`, 131–132 | §2, 134 and 144. Use the same cut in colour w, with the O term determined by $Y_t$. | faithful | It checks only $\eta_t$ for an O term. |
| `Datum.CutZ`, 135–137 | §2, 141–142. The largest value among nonzero z terms is attained at least twice. | faithful | It gives two distinct maximizers among the nonzero terms. |
| `Datum.CutW`, 140–142 | §2, 144. The cut condition also holds in colour w. | faithful | The same maximum condition uses w terms and values. |
| `Datum.IsWeightDatum`, 145–150 | §2, 152–156. Two ultrametrics with real body-pair heights and both cut conditions for every nonempty set of bodies. | differs, harmless | It stores $n\ge2$ explicitly and represents the ultrametrics off the diagonal. The remaining conditions are exact. |
| `cycN`, 157–158 | §7, 360. $N$ is three times the alternating sum over body pairs. | faithful | Each even body pair adds 3 and each odd one subtracts 3 in $\mathbb Z$. |
| `inc`, 162–163 | §7, 361. At an even place, add 2 at both body endpoints or subtract 1 at the body of an O-edge. | faithful | It gives these contributions at the requested index $k$. |
| `cycQ`, 166 | §7, 361. Sum the alternating contributions to $q$. | faithful | It adds the even contribution and subtracts the odd contribution. |
| `degree_two`, 169–172 | §7, 367–368 and 380–382. Every vertex of $B$ incident to an edge has degree at least two. | faithful | It gives a second edge at each endpoint. Step 1 applies before imposing the chamber. |
| `exists_cycle`, 175–176 | §7, 384–385. $E^*$ is nonempty and Step 1 forces a simple cycle. | faithful | The conclusion uses the full simple-cycle predicate. Step 2 needs no chamber for existence. |
| `cycle_relation`, 179–183 | §7, 357–361. Every simple cycle gives $N\Psi^*+q\cdot u=0$ and $N\ne0$ at $\tau\ge2n^2$. | faithful | It states both conclusions for every cycle with the same threshold. |
| `collision_bound`, 186–189 | §7, 363 and §8, 425–426. $\zeta_{tl}+\omega_{tl}\le2M_0+2u_t+2u_l$ for the stated $M_0$. | differs, harmless | The pair-dependent bound agrees. The parameter $\tau$ includes the threshold of D5′. |
| `chamber_nonempty`, 194 | §5, 248. $W_n(\tau)$ is nonempty. | differs, harmless | The padded formulation also has witnesses for $n<2$. |
| `ex2`, 197–203 | §2, 158–160. The two-body example gives the pair and origin heights in terms of $u_0,u_1$. | faithful | It specializes the example to $u=(0,2)$ and equal body-pair heights of zero. |
| `ex2_spec`, 207–213 | §2, 160 and §7, 413. The two maximal edges make a cycle with $N=-3$ and $q=(-2,-3)$. | faithful | It checks the maximum, the complete maximizing edge set, the cycle and the coefficients. |
| `ex3`, 217–223 | §2, 96–103. A colour can have one position of height $+\infty$. | differs, harmless | It supplies an extra example with the same body at O in both colours. |
| `ex3_spec`, 226–227 | §2, 120–127 and 152–156. A zero position suppresses its O-edge from $E^*$, while the cut rules still apply. | differs, harmless | The added example has $P=0$ and checks a suppressed and an admitted O-edge. |
| `ex4u`, 230 | §6, 344–348. Balanced cycles can occur at weights $(0,0,1,1)$ outside the chamber. | faithful | These are the four weights in the remark. |
| `ex4z`, 233 | §6, 344–348. The remark gives the weights of an example with a cycle. | differs, harmless | The test supplies a concrete z tree with inner cluster $\{1,2,3\}$. |
| `ex4w`, 236 | §6, 344–348. The same remark concerns the two trees of the graph. | differs, harmless | The test supplies the w tree with inner cluster $\{0,2,3\}$. |
| `ex4_cycle`, 241–245 | §6, 344–348. A balanced simple cycle occurs at these weights. | faithful | The two ultrametrics give the claimed four-edge cycle of maximal body pairs. |

## Issues and proposed text

The statements can be frozen as written. Two comments can be made more precise.

- **Lines 9–10 and 194.** The padding description is too broad. The nonemptiness assertion is stronger in scope because it also quantifies over $n=0,1$, with a padded $u_1$. A replacement for the sentence about vectors is `A vector is a function on ℕ. For n ≥ 2 its coordinates are the values below n. Chamber also uses u 0 and u 1 on padded inputs at n < 2.`
- **Lines 36–40, 92–98 and 145–148.** Literal `IsUltra` is weaker than requiring $d(x,x)=+\infty$ of the stored function. The node includes its first endpoint directly. The other substantive constraints use distinct vertices. A docstring for lines 36–37 is below. At lines 92 and 96 the corresponding short comments are `/-- ζ on distinct vertices, with ⊤ at (O, O). Body diagonals are padding. -/` and `/-- ω on distinct vertices, with ⊤ at (O, O). Body diagonals are padding. -/`.

```lean
/-- Symmetric ultrametric heights specified on distinct vertices 0, …, N − 1.
The triangle condition is checked on distinct vertices. The mathematical
diagonal is ⊤. Stored diagonal entries serve as padding. -/
```

Lines 191–227 leave two regression cases uncovered. The following additional statements would test them after `ex3_spec`.

```lean
theorem ex3_chamber :
    let D : Datum := { ex2 with
      n := 3
      u := fun k => if k = 1 then 1 else if k = 2 then 20 else 0
      xi := fun t => if t = 0 then 1 else 0
      eta := fun t => if t = 0 then 1 else 0 }
    D.IsWeightDatum ∧ Chamber D.n 18 D.u ∧ D.IsPsiStar (-1) := sorry

theorem ex3_mixed_origin :
    let D : Datum := { ex3 with eta := fun t => if t = 2 then ⊤ else 0 }
    D.IsWeightDatum ∧ ¬ D.IsEdge (1, 3) ∧ ¬ D.IsEdge (2, 3) ∧
      (1, 3) ∉ D.termsZ {1} ∧ (1, 3) ∈ D.termsW {1} ∧
      (2, 3) ∈ D.termsZ {2} ∧ (2, 3) ∉ D.termsW {2} := sorry
```

## Required checks

### 1. Node and diagonal

At line 44 the direction is $d(x,y)\le d(x,p)$. The disjunction includes $x$, even when its stored diagonal is smaller than the height of the edge. The second endpoint passes by reflexivity, including at height $\top$. This computes the brief's node with $d(x,x)=+\infty$.

### 2. Heights at O

At lines 93–98, for $t<n$, both `dz t n` and `dz n t` give $\xi_t$. Both orders in `dw` give $\eta_t$. I checked that `dz n n` and `dw n n` both give $\top$, regardless of `xi n` and `eta n`.

### 3. Edge and term admission

Line 108 admits $(t,O)$ for the maximum exactly when both heights are finite. Line 128 admits its z term for $t\in S$ exactly when $\xi_t$ is finite, regardless of $\eta_t$. Line 132 does the same for $\eta_t$ in colour w. A mixed zero therefore suppresses $\Psi(t,O)$ from the maximum but leaves one cut term available. Cut terms use the direction out of $S$, while graph edges use the canonical order. Symmetry makes the body-pair heights agree. Lines 149–150 restrict $S$ to bodies.

At $n\ge2$, the admitted edge set is finite and contains $(0,1)$. Its real maximum therefore exists for every datum, so `IsPsiStar` adds no restriction on the datum.

### 4. Signs and fallback values

Line 101 negates both coordinate heights and the mass weight. For an O term, lines 119 and 123 negate the mass weight and the own-colour height. For a body pair, minus the valuation of the z term is

$$
-u_t-u_l+\tfrac32(\zeta_{tl}+\omega_{tl})-\zeta_{tl}
=\Psi(t,l)+\omega_{tl}.
$$

The w term adds $\zeta_{tl}$ to $\Psi(t,l)$. A raw call can return the fallback from `WithTop.untopD 0` at a height of $\top$. In the statements, `IsEdge` or `Estar` guards comparisons of `psiE`. The respective term sets guard comparisons of `phiZ` and `phiW`. In the mixed case the admitted cut formula uses only the finite height.

### 5. The existence of two nonzero cut terms

For a nonempty proper $S$, choose $t\in S$ and $l\notin S$. The body-pair term is nonzero in each colour by (F1), §1 line 79, and the masses are nonzero. For $S$ equal to all bodies, (F1) leaves at least $n-1\ge1$ nonzero O terms in each colour. In both cases Lemma A gives a zero sum. A unique term of least valuation could not cancel. There are therefore at least two distinct nonzero terms of largest $\Phi$. Every solution over $K$ in the brief's $n\ge2$ scope satisfies lines 135–142, including when a colour has a body at O.

### 6. Simple cycles

In lines 49–59, `f i` is $e_{2i+1}$ and `g i` is $e_{2i+2}$. They meet on the w side. `g i` meets `f ((i + 1) % r)` on the z side, including the closing pair. The shift permutes $0,\ldots,r-1$, so every z endpoint of a `g` edge is represented among the `f` endpoints. `inj_z` and `inj_w` therefore count $r$ distinct vertices on each side. Equal sets on opposite sides represent different vertices. The edge fields enforce $2r$ distinct edges. At $r=1$ the equations say the two distinct edges are parallel. The predicate has the same strength as the brief's cycle in `cycle_relation`, `exists_cycle` and under the negation in `lemmaC`.

### 7. Cycle coefficients in two cases

Let $S_p$ and $S_O$ be the sums of the signs over body pairs and O-edges. The two height-sum formulas of D4 give coefficient $2S_p-S_O$ on $P$. There are equally many odd and even places, so $S_O=-S_p$ and the coefficient is $3S_p$. At place $i$ the paper gives $2(-1)^i$ at both body endpoints of a body pair and $-(-1)^i$ at the body endpoint of an O-edge. Lines 157–166 compute these by subtracting `f` from `g` in integers.

- At $n=2$, the odd $(0,1)$ contributes $-3$ to $N$ and $(-2,-2)$ to $q$. The even $(1,O)$ contributes $(0,-1)$ to $q$. The result is $N=-3,\ q=(-2,-3)$, as in Lean.
- For an independent $r=2$ example, take $n=4,\ u=(-9,-6,-3,0)$. The z root has height $-12$, with clusters $\{0,2,O\}$ at $-9$ and $\{1,3\}$ at $-4$. Inside $\{0,2,O\}$, the pair $\{0,2\}$ has height $-6$. The w root has height 0 and clusters $\{0,1,O\}$ at 6 and $\{2,3\}$ at 10. All 15 cuts tie in each colour and $P=12$. For $(2,O),(3,O),(0,1),(0,O)$, the z nodes are inner, root, root, inner. The w nodes are root, root, inner, inner. The sole body pair is odd, so $N=-3$. The O-edges add $1$ at body 2 and subtract $1$ at each of bodies 3 and 0. The body pair subtracts $2$ at bodies 0 and 1. Thus $q=(-3,-2,1,-1)$, as in Lean. Its dot product with $u$ is $36=-NP$. The weight vector lies outside the $n=4$ chamber at the D4 threshold.

### 8. The last nonzero index in Lemma B

Lines 29–32 require $m<n$ and $q_m\ne0$. The sum and dot product use `range (m + 1)`, so both include $m$. Read the prefix as a vector with zero entries after $m$. The Lean premises on the raw function are weaker because they allow arbitrary ignored entries there. The mathematical statement is equivalent. The sum-zero premise rules out $m=0$, and `Ico 1 m` gives exactly $1\le j<m$.

The explicit $0\le\tau$ comes from §5's domain for $W_n(\tau)$. It matters because the raw `Chamber` predicate also takes negative parameters. For example, $\tau=-1/2,\ u=(0,2,3/2,1)$ and $q=(-1,-1,0,2)$ meet the other conditions at $m=3$, yet $q\cdot u=0$.

### 9. Collision constant

By D4, $P=-q\cdot u/N$, with $\lvert N\rvert\ge3$ and $\lvert q_j\rvert\le2n-1$. Thus $P\le M_0=(2n-1)\sum_{j<n}\lvert u_j\rvert/3$. Every body pair has $\Psi(t,l)\le P$, so the body height sum is at most $2M_0+2u_t+2u_l$. This is exactly line 189. Replacing the last two terms by $4\max_{j<n}\lvert u_j\rvert$ gives the uniform constant used in the D5′ proof. The parameter $\tau=2n^2$ recovers all the pairs and weights used there.

The finite list of possible maxima in D4 follows from `exists_cycle` and `cycle_relation`. There are finitely many sequences of distinct edges. Each qualifying sequence determines $P$ from $u$.

### 10. Both directions for weight data

Read a Lean datum with its diagonal set to $\top$. A unique least triangle side violates line 40 with that side on the right. A repeated least side passes every permutation. Together with symmetry this gives the brief's ultrametrics. If two O-edges were $\top$ in the same colour, the triangle through O would force their body-pair height to be $\top$ too. That height is real. Thus the restriction to at most one infinite height per colour is already enforced. This also guarantees a nonzero term for the full cut of an abstract datum at $n\ge2$. Proper cuts have a body-pair term.

I tried the raw matrix as a counterexample to the literal diagonal convention. In `ex2`, `dz 0 0` and `dw 1 1` are both 0. This is a literal mismatch if the padding entries are read as heights. Normalizing the diagonal preserves every hypothesis and conclusion in the file.

Conversely, every weight datum in the brief's scope encodes by storing its real off-diagonal body heights and its O-edge heights, with arbitrary real body diagonal padding. Lines 149–150 then ask for the same cuts. Line 146 restricts the predicate to $n\ge2$, the scope of the brief's maximum and Theorem D4. The mathematical definition allows an arbitrary mass vector, with ordering a choice of labels. Realization by a solution of $N_n$ is separate from the definition.

## Counterexample search and nonemptiness

- I used Z3 with exact real arithmetic for $n=2,3,4$, with a flag for every possibly infinite O height. I searched for a simple cycle of maximal body pairs, a maximizing edge with a degree-one endpoint, an acyclic maximizing graph, a cycle violating either part of `cycle_relation`, and a violating body pair for `collision_bound`. I used all nonempty cuts and all cycle lengths allowed by the edge counts. There was no counterexample in these searches. The chamber checks used the minimum allowed $\tau$. Chamber weights increase for $\tau\ge0$, so any larger $\tau$ implies membership at that minimum.
- For Lemma B I searched over all real chamber vectors for each tested prefix, with $1\le m\le4$, $\lvert q_j\rvert\le4$, and $\tau=0,1,8$. There was no counterexample. The premises are satisfiable, for example at $\tau=0$ with $q=(-1,1)$, $m=1$ and $u=(0,2)$. At $n<2$, both versions have no nonzero zero-sum vector. For `lemmaC`, two constant off-diagonal height functions give ultrametrics over any chamber vector.
- For `chamber_nonempty`, take $u_0=0$ and $u_j=(\tau+2)^{j-1}$ for $j\ge1$. The first gap is 1. Every later gap is $(\tau+1)u_{j-1}>\tau u_{j-1}$. This works also for the extra padded cases.
- For the four weight-datum statements, fix any $n\ge2$ and any chamber vector $u$. Set both body-pair heights to $h=u_0/3$. Set $\xi_0=\eta_0=h+u_1-u_0$ and $\xi_t=\eta_t=h$ for $t>0$. All distinct triangles have two least heights. In either colour a body-pair cut value is $2h-u_t-u_l$. If $0\notin S$, take the body $t$ of least mass weight in $S$. The terms $(t,0)$ and $(t,O)$ both attain $-h-u_t$. If $0\in S$, the O term of body 0 attains $-h-u_1$, tied by $(1,O)$ if $1\in S$, or by $(0,1)$ otherwise. These are upper bounds on the other terms in the respective cuts. The edges $(0,1)$ and $(1,O)$ attain $P=-2h-u_1$ and are parallel. This gives simultaneous premises for `degree_two`, `exists_cycle`, `cycle_relation` and `collision_bound` at every admissible $n$ and chamber threshold.

`ex2_spec` is consistent. Every cut has two terms with value $-2$, while $\Psi(0,O)=-4$. The two maximizers have the full vertex set as node in each colour. In `ex3_spec` all admitted terms have value 0. Each proper cut has two body-pair terms, and the full cut has two O terms. For `ex4_cycle` all six body pairs have $\Psi=0$. In the displayed edge order the z nodes are root, inner, inner, root and the w nodes are root, root, inner, inner.

The four test statements exercise basic nonemptiness and the two-body cycle signs. At $n=2$ the chamber's gap inequality for $j\ge2$ has no instances. A test with $n\ge3$ and a weight datum in the chamber is needed to cover the joint premises with an active gap inequality in the test suite. The family above already establishes mathematical nonemptiness. At $n=3$, $u=(0,1,20)$ and $\tau=18$ give a small test with $19>18$. The mixed-origin test uses all real heights 0 and the infinite O heights at different bodies in the two colours. Proper cuts still have two crossing body pairs. Each full cut has two nonzero O terms.

## Independent list and README comparison

I recorded my observations before opening the two requested README sections.

1. Total natural-indexed functions encode finite vectors. The chamber test also accepts two padded coordinates at $n<2$. The O index and canonical edge order agree with README item 1.
2. Lemma B uses the prefix through $m$, interpreted with a zero tail. The nonnegative parameter is already part of §5. This agrees with item 2.
3. Symmetry and the inequalities over distinct triples implement the triangle rule. Item 3 agrees. It omits the stored body-diagonal difference and the explicit inclusion of the first endpoint in `node`.
4. The real branch of $\Psi$ is guarded by both O heights. Each cut guards only its own height. This agrees with items 4–5. The real maximum and its edge set are preserved when $-\infty$ edges are omitted.
5. The tie formulation is equivalent, including for the full cut. Item 6 gives the same conclusion for solution weights. The triangle argument also supplies initial nonzero terms for abstract weight data.
6. Alternating edges, the closing shift and the signs agree with item 7. I also checked the two-parallel-edge case and the two injectivity fields.
7. The first two D4 steps work before imposing the chamber. The bound is the pair-specific inequality in D5′. These agree with item 8. The parameterized bound includes the fixed threshold case.
8. The thresholds are the brief's thresholds, as item 9 says. `IsWeightDatum` makes $n\ge2$ explicit.
9. The examples exercise different parts of the definitions. A joint test at $n\ge3$ and the mixed-colour origin test would add coverage. The reviewer's section asks about the joint case. The family above answers it without relying on the existing tests.

## What I did not check

I reviewed the statements and their correspondence to the specified brief. I did not prove the ten general statements or verify the algebraic-geometric argument for D5′. The counterexample searches were limited to the sizes and parameters listed above. The Lean build checked elaboration and reported the ten `sorry` declarations. Concrete Lean probes checked selected evaluations independently of those declarations.

I did not read `Solution.lean`, `DirectRoute/`, `docs/allN-direct-route-lean-task.md` or the `docs/n7-referee-*.md` files.
