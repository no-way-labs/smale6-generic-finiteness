# R35 release review

*Copy of the report as the session wrote it, with changes to links and to one word: the host name that item A6 quotes is written `[hostname]`, here and in the files of `data/n7/allN/hier/r35/` that quote it. Its links to its own files, which pointed to its working directory, now point to `data/n7/allN/hier/r35/`, where the programs and outputs are kept, and its two links into the release are relative to this directory. 8 links are now plain text because their targets are not kept: the two trial copies of the release with the proposed edits applied, the page images of the PDF, and the copy of the paper of Xia that the session was given, which is the publisher's file. The report read the release built from the paper `docs/as-read/R35-paper.tex`; its prompt is `docs/allN-release-read-prompt-2.md`. Its lists A and B give line numbers of that release.*

**Model.** GPT-6, running as OpenAI Codex. This review is dated 18 November 2026.

**Files opened.** I read all 1,301 lines of the release’s paper, formed my verdict on Sections 2–8, and then opened the release’s review materials. The inventory names every one of the 168 staged files I opened for reading, hashing, rendering, or scanning. The directory ledger below distinguishes those checks. I also read the separately supplied twelve-page xia1991.pdf and the release’s Git status, index entries, branch and remote. To obtain the assignment I opened the specified task file in the starting development workspace. Before its restriction was visible, the same initial read batch returned a Git status listing and searched for an AGENTS.md filename there. That supplied no mathematical evidence. All subsequent project reads used the release and its audit copies. [File inventory](../data/n7/allN/hier/r35/files-opened.txt)

**Verdict on the paper — sound with fixes.** I find the proofs of Theorems 1.1–1.3 sound as printed. The generic-point argument already answers the rationally independent part of Problem 12.4. A linear combination of the position equations supplies a sharper bound of the kind requested in Problem 12.1. Section 11 describes a property of an approximate graph as a property of the exact graph. At the first recorded GP point those graphs differ by the very edge that closes the cycle.

**Verdict on making the repository public today — yes after the changes of list A.** The exact family in Remark 9.1 works. The Table 6 counts and the 96 and 192 hierarchy counts reproduce. Xia’s full paper confirms his ordinary-open-set counting result. A replay of the R30 certificate checker also exposed a hard-coded total of 300/192; the corrected script prints 192/192. The other prepublication changes concern the attribution of 36 complex curves, the scope of the Lean statements, a hostname and checkout paths, licensing of data, and the archive’s links, table rendering and chronology. [Independent exact family](../data/n7/allN/hier/r35/family.log) · [Independent point check](../data/n7/allN/hier/r35/points.log) · [Independent enumeration](../data/n7/allN/hier/r35/count.log)

The entries below give the release line numbers and literal before/after text. Expand an entry for its exact edit. The source patches and an all-edits patch are available as plain text. I applied their replacements only to trial copies. Both list A alone and lists A and B together produced a 22-page PDF with resolved references and no overfull box. After the author’s edits, build the public PDF and regenerate the affected entries of FILES.sha256 from the final files. The published digest of a rebuilt PDF must come from the PDF actually selected for release. [List A patch](../data/n7/allN/hier/r35/list-A.patch) · [List B patch against the original snapshot](../data/n7/allN/hier/r35/list-B.patch) · [Combined source patch](../data/n7/allN/hier/r35/all-source-edits.patch)

The tested list A PDF and manifest form a matching pair. The corresponding PDF and manifest also verify for the combined edits.

## List A — before publication

### A1 · Keep the distinct-valuation question in Problem 12.4

Rationally independent valuations already imply finiteness for arbitrary Hahn masses with those valuations, including series with higher terms. For any nonzero rational polynomial, the valuations of its distinct mass monomials are distinct. Its least-valued term survives. Evaluation therefore lands over the generic point of the rational mass scheme. The proof of Theorem 1.2 excludes that point from \(D\), and Lemma 8.1(a) applies over \(K\). This also covers independent vectors lying outside all the displayed chambers.

<details><summary>paper/alln/main.tex · line 1224 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1224,2 +1224,3 @@
-Does Theorem~\ref{thm:K} hold for all masses in $K$ whose valuations are distinct, or whose valuations
-are linearly independent over $\QQ$?
+Does Theorem~\ref{thm:K} hold for nonzero masses in $K$ with pairwise distinct valuations?
+Rationally independent valuations give a generic mass point by the least-term argument of
+Lemma~\ref{lem:D0}, so finiteness in that case follows from Section~\ref{sec:generic}.
```

</details>

### A2 · State which graph Section 11 actually measured

On 794 records the numerical top set strictly contains the exact top set of the stored decimal heights. In the first GP record (trees 176 and 398), three pairs have score 3.10667 and the origin edge of body 1 has score 3.10666. The latter closes the cycle. On 1,749 records at least one cut has a nonzero gap. The degree-two, cycle, and residual measurements reproduce with the documented tie rule. Calling those graphs the exact graphs of Definition 3.3 gives a false conclusion on actual released records.

<details><summary>paper/alln/main.tex · lines 1123, 1151, 1159 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1123,3 +1123,3 @@
-without the trees and the linear programs, within the tolerance $10^{-3}$, and a third,
-\repo{nk_cycle_check.py}, builds $\Es$ and $\Gamma(\Es)$ at each point and evaluates
-$N\Ps + q \cdot u$ on a basis of the cycles.
+without the trees and the linear programs, within the tolerance $10^{-3}$. A third program,
+\repo{nk_cycle_check.py}, retains edges with $\Ps-\Psi(e)<10^{-3}$ and merges adjacent tree nodes
+whose heights differ by at most $10^{-3}$. It evaluates $N\Ps+q\cdot u$ on a cycle basis of this graph.
@@ -1151,3 +1151,3 @@
-table pass the second program. At each of them every vertex of $\Gamma(\Es)$ lies on two edges, every
-cycle of the basis has $N \ne 0$, and $|N\Ps + q \cdot u| \le 2 \cdot 10^{-5}$; no point lies above the
-bound of the last column. A program written independently by the session that read the release
+table pass the second program. In the graph constructed with these tolerances, every vertex at each
+recorded point has degree two, every basis cycle has $N\ne0$, and its residual satisfies
+$|N\Ps+q\cdot u|\le 2\cdot10^{-5}$. Every recorded maximum is below the corresponding unrounded bound. A program written independently by the session that read the release
@@ -1159,2 +1159,2 @@
-$\tau \ge 43$ for $n = 6$. At the three vectors with a dagger the theorem makes no statement, and the
-relation and the bound hold at every point found.
+$\tau \ge 43$ for $n = 6$. For the three vectors with a dagger, the recorded points satisfy the same residual and bound checks
+outside the theorem's hypotheses.
```

</details>

### A3 · Remove the already attainable target in Problem 12.1

Put \(D=2n+\binom n2\). Write \(F_t^X,F_t^Y\) for the position equations with their right sides subtracted. Pair cancellation gives \(\sum m_tF_t^X=\sum m_tX_t\), and likewise for \(Y\). Choose \(a\) with \(m_a\ne0\). Replacing \(F_a^X,F_a^Y\) by the two linear sums preserves the ideal at these fixed masses. The slice now has \(D-2\) equations of degree at most four and three linear ones. Remark 1.4's own inequality gives \(4^{D-2}\), a factor of 16 better. If every mass vanishes the system is empty. No hypothesis on the sum of the masses is needed.

<details><summary>paper/alln/main.tex · line 1207 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1207,3 +1207,2 @@
-Describe a set $\Sigma_n$ for which Theorem~\ref{thm:Nn} holds, or give a bound for the number of
-solutions of $\cN_n$ modulo the rotation, for masses outside it, that is sharper than the bound of
-Remark~\ref{rem:scope}.
+Give explicit equations, as a function of $n$, for a proper exceptional set $\Sigma_n$ in
+Theorem~\ref{thm:Nn}, or determine the generic number of complex rotation orbits of $\cN_n$.
```

</details>

### A4 · Separate the modified Roberts continuum from Tomar’s 36 complex curves

Tomar’s Theorem 1.1 describes the complex rotation slice. Proposition 3.2(b,c) gives no real configuration points on 30 curves and real points on six. A negative real square root cannot describe points on all 36. This concerns the final illustration in Remark 8.2. Its assertion about the closure of the bad locus holds. [Tomar, Theorem 1.1 and Proposition 3.2](https://hexagonmath.org/pdf/2611.00485v1)

<details><summary>paper/alln/main.tex · line 920 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -920,2 +920,3 @@
-\cite[p.~543 and Remark~8]{albouykaloshin2012}; these solutions are not central configurations, and
-Tomar~\cite{tomarspecial} finds 36 curves of them. If $n - 1$ masses are $0$ and $n \ge 3$, the
+\cite[p.~543 and Remark~8]{albouykaloshin2012}; these signed solutions do not give physical central configurations. Tomar finds 36 irreducible curves
+in the complex rotation slice at these masses. Six have real configuration points, and none contains
+a positive normalised central configuration~\cite[Theorem~1.1 and Proposition~3.2]{tomarspecial}. If $n - 1$ masses are $0$ and $n \ge 3$, the
```

</details>

### A5 · Match the summaries to the exact scope of the formal and computational checks

Table 4 and the abstract limit formal part (d) to the inequality. The type of psi_star_bound contains no finite set. The root README also places the exact verification of Remark 9.1 in a row that currently calls every computation evidence.

<details><summary>paper/alln/main.tex · line 1040 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1040 +1040 @@
-Theorem~\ref{thm:D4}(b), (c) and~(d) in the form printed here. No review asked for a change to the
+Theorem~\ref{thm:D4}(b) and (c) for closed alternating sequences, and the inequality of~(d). No review asked for a change to the
```

</details>

<details><summary>lean/direct-route/README.md · lines 13, 73 · exact replacement</summary>

```diff
--- a/lean/direct-route/README.md
+++ b/lean/direct-route/README.md
@@ -13 +13 @@
-| `ChallengeB.lean` (103 lines) | closed alternating sequences; Lemma 4.1 with the sign; Lemma 5.2; Theorem 6.2 (b), (c), (d) | yes |
+| `ChallengeB.lean` (103 lines) | closed alternating sequences; Lemma 4.1 with the sign; Lemma 5.2; Theorem 6.2 (b), (c) and the inequality of (d) | yes |
@@ -73 +73 @@
-| `DirectRoute/Alt.lean` | Lemma 4.1 with the sign, Lemma 5.2 and Theorem 6.2 (b), (c), (d) in the form of the paper; written by `scripts/allN/lean_gen_alt.py` from `Relation.lean` |
+| `DirectRoute/Alt.lean` | Lemma 4.1 with the sign, Lemma 5.2 and Theorem 6.2 (b), (c) for closed alternating sequences and the inequality of (d); written by `scripts/allN/lean_gen_alt.py` from `Relation.lean` |
```

</details>

<details><summary>README.md · line 31 · exact replacement</summary>

```diff
--- a/README.md
+++ b/README.md
@@ -31 +31 @@
-| The computations of Section 11 | evidence; no proof uses them |
+| The computations of Section 11 | The searches give evidence. The exact calculation in Remark 9.1 verifies its example. The proofs of the theorems, propositions, lemmas and corollaries are independent of these computations. |
```

</details>

### A6 · Remove the machine-specific publication details

The Linux version file includes the container’s actual hostname. The archived prompt gives the author's home-relative checkout and report layout. Both can be removed while keeping the commands, architecture, kernel and audit history intelligible. The other scan hits are classified below.

<details><summary>data/n7/allN/hier/lean/leangate3_cmp_za6lxQYhmPdbSfiCnWljhkD9/versions.json · line 30 · exact replacement</summary>

```diff
--- a/data/n7/allN/hier/lean/leangate3_cmp_za6lxQYhmPdbSfiCnWljhkD9/versions.json
+++ b/data/n7/allN/hier/lean/leangate3_cmp_za6lxQYhmPdbSfiCnWljhkD9/versions.json
@@ -30 +30 @@
- "uname": "Linux [hostname] 6.8.0-138-generic #138~22.04.1-Ubuntu SMP PREEMPT_DYNAMIC Fri Aug  7 13:43:15 UTC  x86_64 GNU/Linux\n",
+ "uname": "Linux [hostname omitted] 6.8.0-138-generic #138~22.04.1-Ubuntu SMP PREEMPT_DYNAMIC Fri Aug  7 13:43:15 UTC  x86_64 GNU/Linux\n",
```

</details>

<details><summary>docs/allN-release-read-prompt.md · lines 13, 19 · exact replacement</summary>

```diff
--- a/docs/allN-release-read-prompt.md
+++ b/docs/allN-release-read-prompt.md
@@ -13,4 +13,2 @@
-**Where you work.** The release is the directory
-`~/Github/smale6-generic-finiteness/smale6-generic-finiteness`. Read only files inside it, and public
-sources on the web. Do not open any other directory of this machine; in particular not
-`~/Github/smale6-dev`. Do not run `git commit`, `git push`, `git checkout` or any command that changes the
+**Where you work.** Use the release directory as your working directory. Read only its files and public
+sources on the web. Keep the development checkout closed. Do not run `git commit`, `git push`, `git checkout` or any command that changes the
@@ -19,2 +17 @@
-**Where you write.** Your report goes to `~/Github/smale6-generic-finiteness/R34-report.md`, one level
-above the repository, and your programs and outputs to `~/Github/smale6-generic-finiteness/r34/`. Create
+**Where you write.** From the release root, write the report to `../R34-report.md` and your programs and outputs to `../r34/`. Create
```

</details>

<details><summary>docs/README.md · line 31 · exact replacement</summary>

```diff
--- a/docs/README.md
+++ b/docs/README.md
@@ -31 +31 @@
-the prompts as given. The write-up read
+the archived prompts. The public copy of the R34 prompt uses relative directory names. The write-up read
```

</details>

### A7 · Make the licence of recorded outputs explicit

The licence texts implement the author's choices. The README assigns the code, paper and documents, but leaves the point sets and logs unassigned, and the top-level CFF lists only MIT. My proposed allocation treats released research data and outputs as documentation. That allocation is a recommendation for the author to adopt, not a statement of an existing grant. The two-identifier CFF below passes the official 1.2.0 schema.

<details><summary>README.md · line 135 · exact replacement</summary>

```diff
--- a/README.md
+++ b/README.md
@@ -135,2 +135 @@
-The code is under the MIT licence (`LICENSE`). The paper and the documents of `docs/` are under CC BY 4.0
-(`LICENSE-CC-BY-4.0`). To cite this work, see `CITATION.cff`.
+The source code, including Lean proofs and programs archived under `data/`, and software configuration files are under the MIT licence (`LICENSE`). The paper, the documents and session reports in `docs/`, and the project's recorded data and outputs in `data/` are under CC BY 4.0 (`LICENSE-CC-BY-4.0`). The preferred paper citation is in `CITATION.cff`.
```

</details>

<details><summary>CITATION.cff · line 9 · exact replacement</summary>

```diff
--- a/CITATION.cff
+++ b/CITATION.cff
@@ -9 +9,3 @@
-license: MIT
+license:
+  - MIT
+  - CC-BY-4.0
```

</details>

### A8 · Make the archive readable at its original targets

The R31 sign-off table contains two extra GFM column delimiters in each of two rows. Its third-line link is broken. Eleven links in the third Lean review open the current paper at obsolete lines. All eleven line numbers identify the intended passages in the R33 snapshot. The archive notice should identify presentation edits and the actual sources of model and commit information.

<details><summary>docs/n7-referee-R31.md · lines 3, 91, 94 · exact replacement</summary>

```diff
--- a/docs/n7-referee-R31.md
+++ b/docs/n7-referee-R31.md
@@ -3 +3 @@
-17 November 2026. I read [the second-read brief](allN-direct-route-second-read.md) at commit `7421729`.
+17 November 2026. I read [the second-read brief](as-read/R31-write-up.md) at commit `7421729`.
@@ -91 +91 @@
-| **S5** | **holds** | Subtracting $u_0$ uses $\sum q_j=0$. For largest index $j>1$, the leading term has absolute value greater than $(1+\tau)|q_j|(u_{j-1}-u_0)$, which dominates the sum of the preceding terms at the stated threshold. For $j=1$ the expression is $q_1(u_1-u_0)$. |
+| **S5** | **holds** | Subtracting $u_0$ uses $\sum q_j=0$. For largest index $j>1$, the leading term has absolute value greater than $(1+\tau)\lvert q_j\rvert(u_{j-1}-u_0)$, which dominates the sum of the preceding terms at the stated threshold. For $j=1$ the expression is $q_1(u_1-u_0)$. |
@@ -94 +94 @@
-| **S8** | **holds** | D4 bounds $v(X_{tl}Y_{tl})$ above by $2M_0+4\max |u_j|$ for all pairs and points. D2 and D0(i) give D5′. The open chamber contains a point outside the countable union of rational hyperplanes, so D0 gives D5 by contradiction and the rational closure argument applies. |
+| **S8** | **holds** | D4 bounds $v(X_{tl}Y_{tl})$ above by $2M_0+4\max \lvert u_j\rvert$ for all pairs and points. D2 and D0(i) give D5′. The open chamber contains a point outside the countable union of rational hyperplanes, so D0 gives D5 by contradiction and the rational closure argument applies. |
```

</details>

<details><summary>docs/allN-direct-route-lean-review-3.md · lines 5, 6, 7, 8, 9, 10, 11, 12, 13 · exact replacement</summary>

```diff
--- a/docs/allN-direct-route-lean-review-3.md
+++ b/docs/allN-direct-route-lean-review-3.md
@@ -5,9 +5,9 @@
-| `IsAltSeq` | “Let $E$ be a set of edges on which $\zeta$ and $\omega$ are real. A closed alternating sequence in $E$ is a sequence $f_0, g_0, f_1, g_1, \dots, f_{r-1}, g_{r-1}$ of $2r$ distinct edges of $E$, with $r \ge 1$, such that $\omega_{f_i} = \omega_{g_i}$ and $\zeta_{g_i} = \zeta_{f_{i+1}}$ for $0 \le i < r$, where $f_r = f_0$.” [Definition 5.1](../paper/alln/main.tex#L516) | The two injectivity fields and cross-family inequality together are equivalent to pairwise distinctness of all $2r$ entries. Both edge sets used here encode each unordered edge once, with increasing endpoints, and supply finite heights. The generic predicate leaves those domain conditions to the caller. The two colour equalities have the paper’s order, and $(i+1)\bmod r$ wraps exactly at $i=r-1$. Positivity rules out an empty sequence. At $r=1$ the conditions still require two distinct edges of equal height in both colours. |
-| `lemmaB_sign` | “Let $n \ge 2$, $\tau \ge 0$ and $u \in W_n(\tau)$. Let $q \in \mathbb Z^n$ be a nonzero vector with $\sum_j q_j = 0$, and let $p$ be the largest index with $q_p \ne 0$. If $\tau \ge \frac{1}{\lvert q_p\rvert} \sum_{1 \le j < p} \lvert q_j\rvert - 1$, then $q \cdot u \ne 0$, and $q \cdot u$ has the sign of $q_p$.” [Lemma 4.1](../paper/alln/main.tex#L483) | Set $p=m$ and interpret the Lean prefix through $m$ as a vector of length $n$ extended by zeros. All sums ignore the tail of the input function. `Ico 1 m` has the required endpoints and the two forms of the quotient agree. The zero sum and $q_m\ne0$ force $m\ge1$, so $m<n$ supplies $n\ge2$. A strictly positive product asserts the same sign and nonvanishing. For $n=2$, $\tau=0$, $u=(0,1)$, $q=(1,-1)$ and $m=1$, the ratio minus one is $-1$ and the product is $1$. |
-| `lemmaC_alt` | “Let $n \ge 2$, $\tau \ge n^2$ and $u \in W_n(\tau)$, and let $\zeta$ and $\omega$ be ultrametrics on the $n$ bodies with real values. Let $E^\circ$ be the set of the pairs of bodies at which $\Psi(a, b) = \tfrac12(\zeta_{ab} + \omega_{ab}) - u_a - u_b$ takes its largest value. Then there is no closed alternating sequence in $E^\circ$.” [Lemma 5.2](../paper/alln/main.tex#L533) | The chamber, threshold, and real ultrametrics match. `psiPair` computes $\Psi$, and `topPairs` includes every maximizing pair. The explicit `hn` matches the paper. For $n<2$ the Lean conclusion would follow from the absence of body pairs. For a genuine input, take $n=4$, $\tau=16$, $u=(0,1,18,324)$ and both heights $17$ on $\{0,2\}$ and $0$ on all other pairs. The chamber and ultrametric conditions hold, and $E^\circ$ contains two pairs, $\{0,1\}$ and $\{0,2\}$. Example 5.4 below shows that the conclusion can fail when the chamber condition is dropped. |
-| `cycle_alt_bodies` | “Two edges with the same node have the same height by Lemma 3.2(a), and hence the conditions on the nodes imply the conditions on the heights.” “Under the hypotheses of Lemma 5.2 the graph $\Gamma(E^\circ)$ has no simple cycle.” [After Definition 5.1](../paper/alln/main.tex#L525), [Corollary 5.3](../paper/alln/main.tex#L540) | This is the implication used to obtain the corollary. `topPairs` supplies distinct endpoints in range. Equal nodes give equal heights under the two ultrametric hypotheses, and `IsCycle` supplies the edge membership, distinctness and wraparound. Thus the implication has the direction needed for `lemmaC_alt` to imply `lemmaC`. The four-body example supplies a source cycle. Its two $\omega$ nodes are the whole body set and $\{0,2,3\}$, and its two $\zeta$ nodes are the whole set and $\{1,2,3\}$. |
-| `alt_relation` | “Let $n \ge 2$, $\tau \ge 2n^2$ and $u \in W_n(\tau)$, and let $(u, \zeta, \omega)$ be a weight datum.” “Every closed alternating sequence in $E^*$ contains an $O$-edge.” “For every closed alternating sequence in $E^*$, the numbers of Definition 6.1 satisfy $N \ne 0$ and $N \Psi^* + q \cdot u = 0$.” [Theorem 6.2(b,c)](../paper/alln/main.tex#L650) | `IsWeightDatum` includes $n\ge2$, both ultrametrics and both cut conditions. `IsPsiStar` identifies $P$ with the attained maximum. `Estar` enforces real heights and increasing endpoints, so second endpoint $n$ is exactly the $O$-edge test. In `cycN` and `cycQ`, $f$ has sign $-1$ and $g$ has sign $+1$. The factors are $3$ in $N$ for a body pair, $2$ per body endpoint in $q$ for a body pair, and $-1$ at the body endpoint in $q$ for an $O$-edge, before applying the sign. These agree with Definition 6.1. The dot product covers all $n$ bodies. The `ex2_alt` row gives a witness to the joint hypotheses. |
-| `cycle_alt` | “Two edges with the same node have the same height by Lemma 3.2(a), and hence the conditions on the nodes imply the conditions on the heights.” In the weight-datum setting, “The graph $\Gamma(E^*)$ has a simple cycle.” [After Definition 5.1](../paper/alln/main.tex#L525), [Theorem 6.2(a)](../paper/alln/main.tex#L653) | This applies the same node-to-height implication to `Estar P`. The full weight-datum hypothesis specializes the general observation to §6 and is already a hypothesis of `cycle_relation`. The local implication uses the ultrametrics and finite heights, and works at any real $\Psi$ level $P$. In particular, at the maximum, the implication allows `alt_relation` to recover `cycle_relation`. The two-body example gives a source cycle, with node $\{0,1,O\}$ for both edges in each colour. |
-| `psi_star_bound` | “The number $\Psi^*$ belongs to a finite set that depends on $n$ and $u$ only, and $\Psi^* \le \tfrac13 (2n - 1) \sum_j \lvert u_j\rvert$.” [Theorem 6.2(d)](../paper/alln/main.tex#L659) | The hypotheses match Theorem 6.2 and the inequality is exact. The uniform finite-set conclusion for fixed $n$ and $u$ is outside the scope of this declaration and should be recorded as absent in the paper’s table. The two-body example satisfies the hypotheses and gives $-2\le2$. With those same weights, assigning height $10$ to every edge in each colour gives maximum $8$ and fails the cut condition on the full body set. |
-| `ex2_alt` | “In Example 3.5 the two edges of $E^*$ form the simple cycle $f_0 = \{0, 1\}$, $g_0 = \{1, O\}$, with $N = -3$ and $q = (-2, -3)$.” [Example 6.4](../paper/alln/main.tex#L743) | This states the alternating-sequence portion at $u=(0,2)$. The values of $\Psi$ on $\{0,1\}$, $\{0,O\}$ and $\{1,O\}$ are $-2,-4,-2$, respectively. The two selected edges have heights $(0,0)$, so the single index checks both equalities. Both ultrametrics have triangle heights $0,0,2$, and each cut has two terms tied at $-2$ in both colours. At $\tau=8$, the chamber condition is $0<2$. This supplies all the hypotheses of `alt_relation` at once. The coefficients evaluate to the paper’s $N=-3$, $q=(-2,-3)$. |
-| `ex4_alt` | “The hypothesis on $u$ is needed, as the following data for $n = 4$ and $u = (0, 0, 1, 1)$ show.” “Then $\Psi = 0$ on all six pairs, and $\{0, 1\}, \{1, 2\}, \{2, 3\}, \{0, 3\}$ is a simple cycle of $E^\circ$.” [Example 5.4](../paper/alln/main.tex#L626) | The type asserts the alternating-sequence portion of the example. The six values of $\Psi$ are all zero. The four successive shared heights are $\omega=0$, $\zeta=2$, $\omega=2$ and $\zeta=0$, the last on the wraparound. Each height function is a real two-level ultrametric. At $\tau=16$, the threshold and all other hypotheses of `lemmaC_alt` hold, and $u_0=u_1$ violates the chamber condition. This is a counterexample to dropping that condition. |
+| `IsAltSeq` | “Let $E$ be a set of edges on which $\zeta$ and $\omega$ are real. A closed alternating sequence in $E$ is a sequence $f_0, g_0, f_1, g_1, \dots, f_{r-1}, g_{r-1}$ of $2r$ distinct edges of $E$, with $r \ge 1$, such that $\omega_{f_i} = \omega_{g_i}$ and $\zeta_{g_i} = \zeta_{f_{i+1}}$ for $0 \le i < r$, where $f_r = f_0$.” [Definition 5.1](as-read/R33-paper.tex#L516) | The two injectivity fields and cross-family inequality together are equivalent to pairwise distinctness of all $2r$ entries. Both edge sets used here encode each unordered edge once, with increasing endpoints, and supply finite heights. The generic predicate leaves those domain conditions to the caller. The two colour equalities have the paper’s order, and $(i+1)\bmod r$ wraps exactly at $i=r-1$. Positivity rules out an empty sequence. At $r=1$ the conditions still require two distinct edges of equal height in both colours. |
+| `lemmaB_sign` | “Let $n \ge 2$, $\tau \ge 0$ and $u \in W_n(\tau)$. Let $q \in \mathbb Z^n$ be a nonzero vector with $\sum_j q_j = 0$, and let $p$ be the largest index with $q_p \ne 0$. If $\tau \ge \frac{1}{\lvert q_p\rvert} \sum_{1 \le j < p} \lvert q_j\rvert - 1$, then $q \cdot u \ne 0$, and $q \cdot u$ has the sign of $q_p$.” [Lemma 4.1](as-read/R33-paper.tex#L483) | Set $p=m$ and interpret the Lean prefix through $m$ as a vector of length $n$ extended by zeros. All sums ignore the tail of the input function. `Ico 1 m` has the required endpoints and the two forms of the quotient agree. The zero sum and $q_m\ne0$ force $m\ge1$, so $m<n$ supplies $n\ge2$. A strictly positive product asserts the same sign and nonvanishing. For $n=2$, $\tau=0$, $u=(0,1)$, $q=(1,-1)$ and $m=1$, the ratio minus one is $-1$ and the product is $1$. |
+| `lemmaC_alt` | “Let $n \ge 2$, $\tau \ge n^2$ and $u \in W_n(\tau)$, and let $\zeta$ and $\omega$ be ultrametrics on the $n$ bodies with real values. Let $E^\circ$ be the set of the pairs of bodies at which $\Psi(a, b) = \tfrac12(\zeta_{ab} + \omega_{ab}) - u_a - u_b$ takes its largest value. Then there is no closed alternating sequence in $E^\circ$.” [Lemma 5.2](as-read/R33-paper.tex#L533) | The chamber, threshold, and real ultrametrics match. `psiPair` computes $\Psi$, and `topPairs` includes every maximizing pair. The explicit `hn` matches the paper. For $n<2$ the Lean conclusion would follow from the absence of body pairs. For a genuine input, take $n=4$, $\tau=16$, $u=(0,1,18,324)$ and both heights $17$ on $\{0,2\}$ and $0$ on all other pairs. The chamber and ultrametric conditions hold, and $E^\circ$ contains two pairs, $\{0,1\}$ and $\{0,2\}$. Example 5.4 below shows that the conclusion can fail when the chamber condition is dropped. |
+| `cycle_alt_bodies` | “Two edges with the same node have the same height by Lemma 3.2(a), and hence the conditions on the nodes imply the conditions on the heights.” “Under the hypotheses of Lemma 5.2 the graph $\Gamma(E^\circ)$ has no simple cycle.” [After Definition 5.1](as-read/R33-paper.tex#L525), [Corollary 5.3](as-read/R33-paper.tex#L540) | This is the implication used to obtain the corollary. `topPairs` supplies distinct endpoints in range. Equal nodes give equal heights under the two ultrametric hypotheses, and `IsCycle` supplies the edge membership, distinctness and wraparound. Thus the implication has the direction needed for `lemmaC_alt` to imply `lemmaC`. The four-body example supplies a source cycle. Its two $\omega$ nodes are the whole body set and $\{0,2,3\}$, and its two $\zeta$ nodes are the whole set and $\{1,2,3\}$. |
+| `alt_relation` | “Let $n \ge 2$, $\tau \ge 2n^2$ and $u \in W_n(\tau)$, and let $(u, \zeta, \omega)$ be a weight datum.” “Every closed alternating sequence in $E^*$ contains an $O$-edge.” “For every closed alternating sequence in $E^*$, the numbers of Definition 6.1 satisfy $N \ne 0$ and $N \Psi^* + q \cdot u = 0$.” [Theorem 6.2(b,c)](as-read/R33-paper.tex#L650) | `IsWeightDatum` includes $n\ge2$, both ultrametrics and both cut conditions. `IsPsiStar` identifies $P$ with the attained maximum. `Estar` enforces real heights and increasing endpoints, so second endpoint $n$ is exactly the $O$-edge test. In `cycN` and `cycQ`, $f$ has sign $-1$ and $g$ has sign $+1$. The factors are $3$ in $N$ for a body pair, $2$ per body endpoint in $q$ for a body pair, and $-1$ at the body endpoint in $q$ for an $O$-edge, before applying the sign. These agree with Definition 6.1. The dot product covers all $n$ bodies. The `ex2_alt` row gives a witness to the joint hypotheses. |
+| `cycle_alt` | “Two edges with the same node have the same height by Lemma 3.2(a), and hence the conditions on the nodes imply the conditions on the heights.” In the weight-datum setting, “The graph $\Gamma(E^*)$ has a simple cycle.” [After Definition 5.1](as-read/R33-paper.tex#L525), [Theorem 6.2(a)](as-read/R33-paper.tex#L653) | This applies the same node-to-height implication to `Estar P`. The full weight-datum hypothesis specializes the general observation to §6 and is already a hypothesis of `cycle_relation`. The local implication uses the ultrametrics and finite heights, and works at any real $\Psi$ level $P$. In particular, at the maximum, the implication allows `alt_relation` to recover `cycle_relation`. The two-body example gives a source cycle, with node $\{0,1,O\}$ for both edges in each colour. |
+| `psi_star_bound` | “The number $\Psi^*$ belongs to a finite set that depends on $n$ and $u$ only, and $\Psi^* \le \tfrac13 (2n - 1) \sum_j \lvert u_j\rvert$.” [Theorem 6.2(d)](as-read/R33-paper.tex#L659) | The hypotheses match Theorem 6.2 and the inequality is exact. The uniform finite-set conclusion for fixed $n$ and $u$ is outside the scope of this declaration and should be recorded as absent in the paper’s table. The two-body example satisfies the hypotheses and gives $-2\le2$. With those same weights, assigning height $10$ to every edge in each colour gives maximum $8$ and fails the cut condition on the full body set. |
+| `ex2_alt` | “In Example 3.5 the two edges of $E^*$ form the simple cycle $f_0 = \{0, 1\}$, $g_0 = \{1, O\}$, with $N = -3$ and $q = (-2, -3)$.” [Example 6.4](as-read/R33-paper.tex#L743) | This states the alternating-sequence portion at $u=(0,2)$. The values of $\Psi$ on $\{0,1\}$, $\{0,O\}$ and $\{1,O\}$ are $-2,-4,-2$, respectively. The two selected edges have heights $(0,0)$, so the single index checks both equalities. Both ultrametrics have triangle heights $0,0,2$, and each cut has two terms tied at $-2$ in both colours. At $\tau=8$, the chamber condition is $0<2$. This supplies all the hypotheses of `alt_relation` at once. The coefficients evaluate to the paper’s $N=-3$, $q=(-2,-3)$. |
+| `ex4_alt` | “The hypothesis on $u$ is needed, as the following data for $n = 4$ and $u = (0, 0, 1, 1)$ show.” “Then $\Psi = 0$ on all six pairs, and $\{0, 1\}, \{1, 2\}, \{2, 3\}, \{0, 3\}$ is a simple cycle of $E^\circ$.” [Example 5.4](as-read/R33-paper.tex#L626) | The type asserts the alternating-sequence portion of the example. The six values of $\Psi$ are all zero. The four successive shared heights are $\omega=0$, $\zeta=2$, $\omega=2$ and $\zeta=0$, the last on the wraparound. Each height function is a real two-level ultrametric. At $\tau=16$, the threshold and all other hypotheses of `lemmaC_alt` hold, and $u_0=u_1$ violates the chamber condition. This is a counterexample to dropping that condition. |
```

</details>

<details><summary>docs/README.md · lines 4, 22, 36 · exact replacement</summary>

```diff
--- a/docs/README.md
+++ b/docs/README.md
@@ -4,3 +4 @@
-produced it. None of this is peer review. Section 13 of the paper describes the sessions; this directory
-holds what they were given and what they wrote. The reports are unchanged, with one exception that the
-report R34 states in its second line.
+produced it. None of this is peer review. Section 13 of the paper describes the sessions. This directory holds the reports, surviving prompts and the six texts listed below. Release edits retarget the R31 brief link, the third Lean review’s line links and R34’s links to its outputs, and repair the rendering of two R31 table cells. The review verdicts are preserved.
@@ -22,2 +20 @@
-The model names are those of the author's configuration. A report names its model as far as the session
-could identify it; R32, R33 and R34 say "GPT-6" and that the variant was not visible to them.
+The model names are those of the author's configuration. R32, R33 and R34 identify GPT-6 and say that the serving variant was unavailable. Several other reports give no model name.
@@ -36,2 +33 @@
-- The texts of `as-read/` are the versions that the referees judged. Each report states a commit of the
-  development repository; the file here is the text at that commit. They are earlier than the paper and
+- The texts of `as-read/` are the versions that the referees judged. The R29, R31, R32 and R33 reports identify development commits. R30 identifies its brief and R34 identifies its release snapshot. They are earlier than the paper and
```

</details>

<details><summary>paper/alln/main.tex · line 1246 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1246,2 +1246 @@
-GPT-6.2 Sol (OpenAI) at its highest setting of reasoning effort. These names are those of the author's
-configuration; each report names its model as far as the session could identify it. Three sessions read earlier write-ups
+GPT-6.2 Sol (OpenAI) at its highest setting of reasoning effort. The model names and reasoning settings are from the author's configuration. Several reports also identify the model family visible to the session. Three sessions read earlier write-ups
```

</details>

### A9 · Give the substantive findings of the archived readers

R29 found a false ancillary assertion about four-body origin strata and a faulty tree filter, and R31 rejected the unqualified six-body minimum for a balanced cycle. R33 reviewed changes, while R34 read the whole draft. A dated account also remains accurate after R35. The present source’s two-sided cherry test implements the R29 fix.

<details><summary>paper/alln/main.tex · lines 1251, 1275, 1288, 1291 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1251,2 +1251,2 @@
-Each of the three reported that it found no error and asked for corrections of wording and of detail,
-which were made. The third searched the literature and found that the survey of the working agent had
+All three accepted the main proof after clarifications. R29 also found a false assertion about the
+four-body origin strata and a faulty tree test. R31 corrected the scope of a six-body cycle count. The third searched the literature and found that the survey of the working agent had
@@ -1275 +1275 @@
-Sections~\ref{sec:lean} and~\ref{sec:llm}, and for corrections to the instructions of the repository, all of which were made. It recomputed the recorded points and the exact searches with programs of its own
+Sections~\ref{sec:lean} and~\ref{sec:llm}, and to the instructions of the repository. The release incorporates the revisions described here. It recomputed the recorded points and the exact searches with programs of its own
@@ -1288,2 +1288,2 @@
-that those sessions read. The three sessions that read drafts of this paper judged these proofs as
-printed in those drafts, and the third of them read every section. After its report the text changed
+that those sessions read. R32 examined the proofs assigned in its draft, R33 checked the revisions, and R34 read every
+section of its draft. After its report the text changed
@@ -1291,2 +1291 @@
-the family of weight data and its check, was written after that report, and no separate session has
-read it or the other last changes. For the statements of Table~\ref{tab:lean} that have a formal counterpart, the
+the family of weight data and its check, postdates all nine reports archived here. For the statements of Table~\ref{tab:lean} that have a formal counterpart, the
```

</details>

### A10 · Limit the introduction’s description of Xia to its finiteness conclusion

Xia treats two or three large masses and successively smaller remaining masses. Section 3 states exact planar counts on open subsets of the full positive mass space. Section 4 proves that masses admitting a degenerate configuration have positive (n−1)-dimensional Hausdorff measure for n≥4. The phrase in the introduction attributes a limitation to the entire paper that applies only to its counting result. Xia, full text, pp. 168–179 · [Publisher record](https://doi.org/10.1016/0022-0396(91)90137-X)

<details><summary>paper/alln/main.tex · lines 125, 133 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -125 +125 @@
-all & some open sets of positive masses in the usual topology & Xia~\cite{xia1991} & published; the configurations are counted \\
+all & some open sets of positive masses in the usual topology & Xia~\cite{xia1991} & published; exact planar counts up to direct similarity \\
@@ -133,2 +133,3 @@
-for any $n \ge 7$. The results of Xia and of Moczurad and Zgliczy\'nski hold at the equal masses or on
-open sets of masses in the usual topology, and say nothing outside them. Of the two claims for every $n$, one was withdrawn and the other is a record of which we could read the title only. The following theorem gives finiteness outside a proper algebraic
+for any $n \ge 7$. Xia counts configurations on certain open sets of positive masses. Moczurad and Zgliczy\'nski give
+counts at and near equal masses. Neither counting result establishes finiteness on a Zariski-open
+set of masses for $n\ge7$. Of the two claims for every $n$, one was withdrawn and the other is a record of which we could read the title only. The following theorem gives finiteness outside a proper algebraic
```

</details>

### A11 · Report the actual Farkas certificate count on replay

This R30 script imports the current survivor set but hard-codes 108 earlier successes. On the 192 independently reconstructed ordered inputs, the first pass certified zero and the fallback certified all 192. The shipped final line then printed “total 300/192”. The exact certificate checks hold. Only the displayed total needs the actual survivor count and residual failure count. The archived R30 report can retain its historical breakdown.

<details><summary>data/n7/allN/hier/r30/cert6b.py · line 89 · exact replacement</summary>

```diff
--- a/data/n7/allN/hier/r30/cert6b.py
+++ b/data/n7/allN/hier/r30/cert6b.py
@@ -89 +89 @@
-print(f"newly certified: {ncert}/{len(fails)}; total {108+ncert}/192")
+print(f"newly certified: {ncert}/{len(fails)}; total {len(surv) - len(still)}/{len(surv)}")
```

</details>

## List B — soon after publication

### B1 · Cite the corrected scope of affine Bézout and annotate the historical wording

The present application uses closed hypersurfaces and their closed intersections. Heintz's original Theorem 1 on p. 251 prints a broader assertion for constructible sets. His 1985 correction matters for readers following the R34 report, which explicitly invokes that broader version. The corrected inequality suffices here. [Original paper](https://www.academia.edu/76016550/Definability_and_fast_quantifier_elimination_in_algebraically_closed_fields) · [Corrigendum](https://doi.org/10.1016/0304-3975(85)90150-1) · [Pardo and Sebastián, Theorem 2.14 and Example 2.15](https://arxiv.org/pdf/2012.15296)

<details><summary>paper/alln/main.tex · line 189 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -189 +189 @@
-space~\cite[Theorem~1]{heintz1983} bounds the degree of their set by the product of these degrees, and
+space~\cite[Theorem~1, p.~251, with the corrigendum]{heintz1983} bounds the degree of their set by the product of these degrees, and
```

</details>

<details><summary>paper/alln/references.bib · line 127 · exact replacement</summary>

```diff
--- a/paper/alln/references.bib
+++ b/paper/alln/references.bib
@@ -127,0 +128 @@
+  note    = {Corrigendum, Theoret. Comput. Sci. 39 (1985), 343},
```

</details>

<details><summary>docs/README.md · line 53 · exact replacement</summary>

```diff
--- a/docs/README.md
+++ b/docs/README.md
@@ -53 +53 @@
-  it read it; the READMEs, which it also read, have changed since in the places that its report names.
+  it read it. The READMEs have also changed. R34’s discussion of Heintz quotes the original constructible-set statement. The 1985 corrigendum qualifies that statement, and Remark 1.4 uses only closed sets.
```

</details>

### B2 · Specify the modified weight, the threshold examples and the sampled searches

The repeated-weight example shows why some restriction is needed. The proof itself supplies smaller sufficient constants. The binary trees parametrize finite heights, with weak height inequalities allowing multifurcations. Sampling, branching limits and numerical LPs restrict the searches. R30 and R31 carried out different large-size experiments. The free-multiplier formula uses a modified score on origin edges and requires a nonzero multiplier. With the original Definition 3.3 the telescoping identity is purely combinatorial and has no multiplier term.

<details><summary>paper/alln/main.tex · lines 940, 942, 1112, 1181 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -940 +940 @@
-the left sides $X_t$, $Y_t$ of \eqref{eq:N2}, \eqref{eq:N3} & the $O$-edges. With left sides $\theta X_t$, $\theta Y_t$ and a further unknown $\theta$, Step~2 has the additional term $(N/3)\, v(\theta)$, $\Ps$ is not bounded, and the system has a continuum by scaling \\
+the left sides $X_t$, $Y_t$ of \eqref{eq:N2}, \eqref{eq:N3} & the $O$-edges. With a free multiplier $\theta\ne0$, use $\Psi(t,O)=-v(\theta)-u_t-\xi_t-\eta_t$. Step~2 then adds $(N/3)v(\theta)$ to the relation. Scaling any solution gives unbounded $\Ps$ and infinitely many rotation orbits \\
@@ -942 +942 @@
-$u \in W_n(\tau)$ with $\tau \ge n^2$ & Lemma~\ref{lem:C}, Steps~1 and~4; Example~\ref{ex:0011} shows that it is needed there \\
+$u \in W_n(\tau)$ with $\tau \ge n^2$ & Lemma~\ref{lem:C}, Steps~1 and~4; Example~\ref{ex:0011} shows failure without a restriction on the weights \\
@@ -1112 +1112 @@
-condition. It therefore covers the weight data in which every $\xi_t$ and every $\eta_t$ is real. The
+condition. These tree pairs parametrise the stratum where every $\xi_t$ and $\eta_t$ is real, allowing adjacent nodes to have equal heights. The
@@ -1181,2 +1181,2 @@
-$n \ge 7$: the second and the third separate session sampled pairs of hierarchies for seven and eight
-bodies and tested particular cycles for $8$ to $13$ bodies, and their reports describe these searches.
+$n \ge 7$: R30 sampled pairs of hierarchies for seven and eight bodies, and R31 tested particular cycles for
+$8$ to $13$ bodies. Their reports describe these searches.
```

</details>

### B3 · Distinguish the archived Lean evidence from the author’s run history

The three Linux logs show the comparator invocations and six acceptances each. The release has no matching macOS transcript or mutation-control transcripts. The root instructions correctly disclose disabled sandboxing. A digest mutation can be checked before any Lean build.

<details><summary>paper/alln/main.tex · line 1046 · exact replacement</summary>

```diff
--- a/paper/alln/main.tex
+++ b/paper/alln/main.tex
@@ -1046,3 +1046,3 @@
-reader compare the three statement files without it. Two controls were run: with a \repo{sorry} placed in one
-proof the check fails, and with a false hypothesis added to a statement the check fails because the
-statement file differs from the fixed one.
+reader compare the three statement files without it. In two further runs we observed rejection after inserting a \repo{sorry} into a proof and a digest
+mismatch after adding a false hypothesis to a fixed statement. The archived transcripts document
+the Linux comparator runs.
```

</details>

<details><summary>README.md · line 77 · exact replacement</summary>

```diff
--- a/README.md
+++ b/README.md
@@ -77,2 +77 @@
-bubblewrap and unprivileged user namespaces you can leave `--local` out. We ran the gate on macOS (ARM)
-and on Linux (x86-64), both without the sandbox; on our Linux machine the sandbox could not be started.
+bubblewrap and unprivileged user namespaces you can leave `--local` out. We ran the comparisons on macOS (ARM) and Linux (x86-64). Both successful runs used the unsandboxed option. On the Linux host, namespace creation failed in the sandboxed runs.
```

</details>

### B4 · Make the README comparison literal and keep its third executable out of Git

The first two output files have a compiler-command header and a timing footer. All seven mathematical lines matched byte for byte. The third executable is called cycles and the stock ignore rules omit it.

<details><summary>README.md · line 124 · exact replacement</summary>

```diff
--- a/README.md
+++ b/README.md
@@ -124,2 +124 @@
-The expected outputs of the first two are the `.txt` files next to them, and that of the third is the first
-eleven lines of `independent_cycles.log`. The third also gives the 96 cycles of six bodies of Section 11
+The seven output lines of each of the first two programs are lines 2–8 of its adjacent `.txt` file. The third program prints the first eleven lines of `independent_cycles.log`. The third also gives the 96 cycles of six bodies of Section 11
```

</details>

<details><summary>.gitignore · line 16 · exact replacement</summary>

```diff
--- a/.gitignore
+++ b/.gitignore
@@ -16,0 +17 @@
+/cycles
```

</details>

### B5 · Document the scope of the historical ray flags

The ray routine samples objectives on a cone intersected with a box and skips nonoptimal solver statuses. A box vertex need not span an extreme ray. A fixed projection can miss a recession direction perpendicular to it. These flags do not enter Section 11’s counts or the proof. Retain the hash-matched as-run programs and explain the flags at the point of reuse.

<details><summary>README.md · line 115 · exact replacement</summary>

```diff
--- a/README.md
+++ b/README.md
@@ -115 +115 @@
-there. `versions.json` in each directory holds the SHA-256 digest of the program that the run used.
+there. `versions.json` in each directory holds the SHA-256 digest of the program that the run used. The historical `ray` flags describe directions found by floating-point searches with selected objectives. A zero flag means the search found no qualifying direction. The one-projection `--far` diagnostic and these flags provide no certificate of boundedness.
```

</details>

## What I did not check

The Lean build, the Mathlib cache and a fresh comparator run were excluded by the assignment. I verified the statements, pins, proof-source scan and the archived Linux transcripts. The macOS acceptances and the two historical mutation controls are author-reported. The additional historical R30 Python census hit the local time limit. I completed its mathematical count independently and used those witnesses to exercise the downstream checks. I did not reconstruct the six long, original floating-point searches, verify their hardware independently, or audit the kernels, Mathlib, HiGHS or all cited proofs. I compared the assertions about other papers with their primary statements. Heintz’s original theorem text was readable. The 1985 correction was identifiable at its publisher, and I checked its mathematical restriction in Pardo and Sebastián’s full text and by a counterexample below. I could not obtain a readable facsimile of that one-page corrigendum. Okolo’s proof is restricted. The search for prior work is limited to identifiable public sources as of 18 November 2026. The historical reviewers’ identities, model settings and private session isolation cannot be independently authenticated from the archive.

## Referee sheet

| Item | Verdict | Basis |
| --- | --- | --- |
| H1 | **holds** | All four statements of Section 2, the node lemma, both cut identities and both directions of the normalization/orbit comparisons check out. |
| H2 | **holds** | The coefficient bounds cover wraparound and the crossed choices at the lightest body. The repeated-mass control gives the stated four-edge cycle. |
| H3 | **holds** | The origin-free child makes every required cut score finite. The unique origin edge at a body forces an odd coefficient. Parts (a)–(d), Corollary 6.3 and Example 6.4 follow. |
| H4 | **holds with a fix** | The dimension, slice, base-change and density arguments prove Theorems 1.1–1.3. Clarify which of Tomar’s curves contain real points in the illustration in Remark 8.2 (A4). |
| H5 | **holds** | Independent exact decomposition of the whole parameter line. The datum and specified sequence work precisely for \(\chi\ge3\). The released program establishes its stated strict range. |
| H6 | **holds with a fix** | Remark 1.4 is valid for closed affine intersections. The corrected literature scope, the multiplier convention and the threshold wording are in B1–B2. Remark 9.2 accurately describes the local families. |
| H7 | **holds with a fix** | All 28 TeX diff hunks and both BibTeX hunks are covered below. The new numerical-graph wording, scope of historical reviews, and one literature qualification need edits. |
| H8 | **holds with a fix** | The abstract’s theorem and formalization boundary hold. Two disjuncts in the stated problems already have answers. The records support the narrower historical and literature wording in A1, A3, A8–A10. |
| H9 | **holds with a fix** | All 22 declarations and all nine trusted digests match. No listed token occurs in the 14 proof files. The unqualified reference to all of (d) at line 1040 conflicts with its formal type and Table 4 (A5). |
| H10 | **fails** | The first operational mismatch is the statement beginning on lines 1123–1125 that the third program “builds \(\mathcal{E}^{*}\) and \(\Gamma(\mathcal{E}^{*})\) at each point”. It includes near-maximizers. All six numerical rows and both enumerations reproduce under the programs’ actual definitions (A2). |
| H11 | **holds with a fix** | Every permitted root command ran. The R31 target and eleven historical line links need the corrections in A8. The first two output references include a header and a footer (B4). The expected prepublication GitHub 404 is excluded. |
| H12 | **fails** | The Linux version record names its host, the archived prompt exposes checkout paths, and two GFM rows split in the middle of formulas. The historical certificate script can also print 300/192. These are concrete hits (A6, A8 and A11). |
| H13 | **holds with a fix** | The preferred citation is valid, the release tree matches the staged blobs, and both licence texts are present. Assign the data and describe both licences in CFF (A7). |
| H14 | **holds with a fix** | Xia’s full text supports the planar exact counts on Euclidean-open sets in all mass parameters. Its degeneracy theorem motivates A10. I found no accessible prior proof of the unrestricted generic planar result for any \(n\ge7\), or counterexample to 1.2 or 1.3. The withdrawn and restricted claims are accounted for. |

## Independent reading of the proofs

I judged Sections 2–8 from the current manuscript before looking at the earlier readers’ reports. The statements read in dependency order give a short argument. Lemma 3.4 takes a solution to a weight datum. Theorem 6.2 bounds its maximum, and Corollary 6.3 passes the bound to each squared distance. Proposition 7.1 and Lemma 2.4 turn that into orbit finiteness. Lemma 8.1 passes from a Hahn point lying over the generic point to a rational exceptional hypersurface. Lemmas 2.1–2.2 return to physical similarities. A reader needs the preceding definitions for \(W_n\), the rotation, the cut scores, and the two meanings of cycle. Corollary 5.3 and the examples deliberately refer back. With their stated references and Table 2, no premise of the main implication is left in a computational section.

### Sections 2 and 3

- **Lemmas 2.1 and 2.2.** After multiplying by \(m_t\overline{z_t-c}\), each pair contributes \(m_tm_l/r_{tl}\). As \(I,U>0\), the multiplier is positive. Summation with the mass weights gives the centre of mass. The multiplier scales as length to the power \(-3\), so the prescribed dilation normalizes it. Noncollision makes the multiplier unique, by subtracting the equations of two positions if necessary. Substitution and conjugation give the two polynomial position equations. If two physical lifts are in one complex rotation orbit, some \(z_t\ne0\) forces \(s\bar s=1\). The injection before identifying reflections suffices.
- **Lemmas 2.3 and 2.4.** Equation (1.2) makes all three factors units on the solution set and permits at most one zero position in each colour. A stabilizer fixes the nonzero \(X_{01}\). On each component \(C\), the closure of the image of \(\mathbb G_m\times C\) is irreducible and contains \(C\), hence equals \(C\). Every orbit has dimension one. Each orbit in a one-dimensional component contains an open subset of that component, so there can be only one. This also excludes zero-dimensional components and deals with the empty variety.
- **The Hahn field and Lemma 3.2.** The real value group is divisible, the coefficient field is algebraically closed, and the Hahn construction has the required algebraic closure property. For real \(h\), a node is the same threshold ball around either endpoint. Its generating pair has the minimum internal height \(h\). The strict inequality \(d>h\) gives the children, and a pair between children has height exactly \(h\). A pair leaving the node has height below \(h\). Two applications of the ultrametric inequality recenter the same threshold ball in (d). Repeated indices and coincident positions in one colour respect the infinite diagonal convention. [Poonen, Theorem 1 and Corollary 4](https://math.mit.edu/~poonen/papers/amsval.pdf)
- **Definition 3.3, Lemma 3.4 and Example 3.5.** Antisymmetry cancels internal forces after multiplication by the masses. The negative valuation of a crossing \(X\)-term is \((\zeta+3\omega)/2-u_t-u_l=\Psi+\omega\). The origin term is admitted whenever \(X_t\ne0\), independently of \(Y_t\). A proper nonempty cut has a nonzero pair term, and the cut of all bodies has a nonzero position term. Thus the nonarchimedean minimum is tied. Interchanging colours gives the second cut. For two bodies subtraction gives \(P^3(m_0+m_1)=1\). The positions are \(m_1 X_{01}/(m_0+m_1)\) and \(-m_0 X_{01}/(m_0+m_1)\), and similarly for \(Y\). When \(u_0<u_1\), this gives both printed active edges, their common root nodes and the claimed gap.

### Sections 4 and 5

- **Lemma 4.1 and Remark 4.2.** Translation by \(u_0\) removes the zeroth coefficient because the sum of coefficients vanishes. For \(p=1\) the sign is immediate. For \(p\ge2\), the earlier weighted sum is bounded by \((1+\tau)|q_p|(u_{p-1}-u_0)\), strictly smaller than the last term in magnitude. Equality in the hypothesis on \(\tau\) is allowed. At \((0,2,3/2,1)\) both gap inequalities for \(\tau=-1/2\) hold, the coefficient threshold is \(-1/2\), and the dot product vanishes.
- **Definition 5.1 and Lemma 5.2, Step 1.** The alternating matching is by height. Matching nodes gives the stronger simple-cycle condition, including a two-edge cycle in the multigraph. Subtract the two equations at each \(i\) and sum cyclically. The incidence difference sums to zero at the mass vector, has coefficient sum zero, and each coefficient has magnitude at most \(n-1\), because the edges are all distinct. Lemma 4.1 forces the entire vector to vanish.
- **Step 2.** The prefixes \(a(i)\) have sum zero and \(b(i)=a(i)-\mathbf1_{f_i}\) has sum \(-2\). Telescoping fixes \(\alpha_i=\alpha_0+2a(i)\cdot u\); substitution gives \(\beta_j=2\Psi^\circ-\alpha_0-2b(j)\cdot u\). An interval of the signed incidence list, with either order of its endpoints, uses at most \(n-1\) different pairs through a body. Adding back the single \(f_j\) indicator gives the asserted bound \(n\). The endpoint \(i=r\) is valid because \(a(r)=a(0)\).
- **Steps 3 and 4.** At the largest participating index \(L\), balance gives a genuinely nonconstant cyclic walk with steps \(0,\pm1\). A down-step enters its minimum and an up-step leaves that level. They can belong to different visits to the minimum. This gives the two low and the two high levels in (5.3), even across the wrap. The two partners of \(L\) are distinct. The two coordinatewise triangle minima yield one of four height sums. An uncrossed choice would put \(u_L\) below one of its smaller-index partners. For either crossed choice the comparison vector has sum zero, support ending at \(L\), coefficient \(-1\) there, and every coefficient bounded by \(n+1\). The earlier-coefficient sum is at most \((n-2)(n+1)\), so Lemma 4.1 gives the wrong sign for (5.4). Ties among the minima and \(r=1\) present no exception.
- **Corollary 5.3 and Example 5.4.** Shared nodes imply shared heights. In the repeated-mass example each of the six pair scores is zero. The four edges meet root/cluster nodes in the prescribed order, with distinct nodes on each side. The independent rank search recovers its edge set once among the 82 feasible control cycles. [Exact examples](../data/n7/allN/hier/r35/family.py) · [Enumeration](../data/n7/allN/hier/r35/count.log)

### Section 6

1. **Theorem 6.2(a).** Choose an endpoint child of the \(\omega\)-node excluding \(O\); it is nonempty and contains bodies only. A crossing edge reaching another child has \(\omega=h\). An edge leaving the node has \(\omega<h\). If \(\eta_p=+\infty\), \(p\) and \(O\) would belong to the same child, so such an origin edge cannot cross this cut. Thus even the one-colour admissibility rule gives a finite \(\Phi^z=\Psi+\omega\) whenever that equality is used. The active edge attains \(\Psi^*+h\). A second cut term ties it, forcing both maximal \(\Psi\) and the very same \(\omega\)-node. Interchanging the colours and closing a longest vertex-simple path gives a simple cycle, including parallel edges.
2. **The relation.** In a closed alternating sequence the two height sums cancel. If \(\sigma\) is the signed body-pair count, the signed origin-edge count is \(-\sigma\). Thus the coefficient of \(\Psi^*\) is \(3\sigma=N\), and \(\sum q_j=5\sigma\). This identity by itself uses no chamber hypothesis.
3. **Part (b).** If a body pair attains the global maximum then \(\Psi^\circ=\Psi^*\). An all-body alternating sequence survives restriction to the two body ultrametrics with the same heights, so Lemma 5.2 excludes it.
4. **Part (c).** At the body of any participating origin edge, that edge occurs exactly once. Every body-pair contribution to \(q_t\) is even, so \(q_t\) is odd. If \(N=0\), this nonzero vector would be both balanced and orthogonal to \(u\). Since \(|q_j|\le 2n-1\), at most \(n-2\) earlier coefficients enter the dominance test. The chamber rules out orthogonality.
5. **Part (d), Corollary 6.3 and Example 6.4.** There are finitely many sign lists of distinct edges. For the cycle supplied by (a), \(|N|\ge3\), and the triangle inequality gives the displayed uniform bound on \(-q\cdot u/N\). Substituting the formula for a pair score gives the collision bound for every pair. At two bodies the orientation in the example gives \(N=-3,\ q=(-2,-3)\) and the stated identity.

### Sections 7 and 8

- **Proposition 7.1.** A nonconstant regular function \(X_{tl}Y_{tl}\) on an irreducible affine component has cofinite image on \(K\)-points by constructibility. Infinitely many \(aT^{M+1}\) are available, contradicting the bound. Thus every such product is a nonzero constant and every \(P_{tl}\), with at most two possible values, is constant there. Dividing by \(X_{ab}\) identifies the component with \(\mathbb G_m\) times its slice. For each third body the two fixed products give a quadratic in \(X_{ca}\) with leading coefficient \(-\delta_{ab}\ne0\). It has finitely many roots even with a repeated root. This fixes finitely many differences. The position equations then give finitely many coordinates, including for \(n=2\). This last step works even when the total mass vanishes. A finite slice contradicts dimension at least two. Theorem 1.3 follows by taking one bound for the finitely many pairs and applying Lemma 2.4.
- **Lemma 8.1(a).** The upper semicontinuity used is on the source of the finite-presentation morphism. Take the closed locus where the dimension of a component of the fibre through the point is at least two, then take its constructible image \(D\). For a field extension above a mass point, each point of the old fibre lifts, and the specified fibre dimension agrees upstairs. This avoids confusing fibre dimension at a point with the dimension of its local ring. Geometric components over an algebraically closed field have dense closed points. The orbit criterion now gives precisely membership in \(D\). [Stacks 02FZ](https://stacks.math.columbia.edu/tag/02FZ) · [02FY, parts 1 and 3](https://stacks.math.columbia.edu/tag/02FY) · [054K](https://stacks.math.columbia.edu/tag/054K)
- **Lemma 8.1(b) and Theorems 1.2 and 1.1.** A dense constructible set contains the generic point of the irreducible mass scheme. In the nonempty open chamber one can avoid the countably many rational hyperplanes. Distinct exponent vectors then give distinct valuations of monomials. For the monomial masses the ring map is injective and its image point is generic. Finiteness in \(K\) puts this point outside \(D\), hence some nonzero rational mass polynomial vanishes on \(D\). Its complex hypersurface is proper, and (a) plus physical normalization gives the two generic statements. The same least-term test works for arbitrary masses with rationally independent valuations, as recorded in A1. [Stacks 005K](https://stacks.math.columbia.edu/tag/005K)
- **Remark 8.2.** Constructibility supplies an open part of the closure dense on every component. Flat extension of fields and restriction to the open torus send minimal primes upstairs to minimal primes downstairs, so every surviving component meets that open part. For a nonempty valuation fibre on an irreducible torus subvariety, Payne’s density gives a point in that open part at the same valuation vector. Lemma 8.1(a) and Theorem 1.3 then contradict each other. The assertion concerns the closure of \(D\), which can be smaller than the particular hypersurface chosen to contain it. A valued-field embedding preserves distinct orbits, as the unique slice representative shows. The signed Roberts continuum and the freely moving massless bodies illustrate different fixed exceptional masses. A4 specifies the real content of Tomar’s complex count. [Payne, Corollary 4.2](https://arxiv.org/abs/0705.1732) · [Erratum, Remark 2](https://web.ma.utexas.edu/users/sampayne/pdf/CorrectionToFibers.pdf)

### Remarks 1.4, 9.1 and 9.2, and Table 3

**Remark 1.4.** With the masses fixed, \(D=2n+\binom n2\) is the number of unknowns and of equations when each unordered pair is counted once. Each polynomial has degree at most four. Equation (1.2) makes \(X_{01}\) invertible and the unique rotation into the degree-one slice has multiplier \(X_{01}^{-1}\). Iterate the affine degree inequality on closed hypersurfaces, including the slice. The degree of a finite reduced set is its cardinality, and the empty set poses no problem. This proves the printed \(4^D\). Heintz states the intersection inequality in Theorem 1 on printed p. 251. The correction is TCS 39 (1985), p. 343. Locally closed sets, in particular closed sets, have the needed inequality. For the danger with arbitrary constructible sets, take the complement of a line in the affine plane and add back two points on that line. Its closure has degree one, yet its intersection with the line has degree two. No quotient, elimination-degree estimate, isolated-solution multiplicity, or theorem about an arbitrary constructible image is needed here. A3 gives the smaller bound directly. [Heintz](https://doi.org/10.1016/0304-3975(83)90002-6) · [Corrected scope and counterexamples](https://arxiv.org/pdf/2012.15296)

**Remark 9.1.** I transcribed the printed heights before inspecting the author’s program. My program forms the 20 triangle tests, 30 cut tests, nine finite edge-score tests and four matching-height equalities. For every predicate it takes *all* pairwise crossings of its rational affine forms. The exact midpoint of each resulting interval, a point on each unbounded interval, and every singleton breakpoint decide the whole real line because every atomic sign is constant on each open cell. Infinity is a separate symbol, and each cut admits its origin term according to its own colour. The combined predicate is true precisely on \([3,\infty)\). For an explicit obstruction below 3, the \(w\)-cut of \(\{1\}\) has scores \(-(3\chi+9)/2,\,-(3\chi+15)/2,\,-\chi-6,\,-\chi-6\) on \(01,12,13,1O\). The first is the unique maximum for every \(\chi<3\); at 3 it joins the last two. The four maximum edges are \(02,2O,0O,03\). The \(w\)-heights agree within the two indicated pairs, the \(z\)-heights agree across them, and signs \(-,+,-,+\) give \(N=0,\ q=(1,0,-3,2)\) and \(q\cdot u=0\). The bound in 6.2(d) at this \(u\) would be 14, while \(\Psi^*=\chi\) is unbounded. The finite-set assertion fails as well. The coordinate index \(p=3\) gives Lemma 4.1’s threshold \(3/2-1=1/2\). The vector \(u\) itself belongs to \(W_4(\tau)\) only for \(0\le\tau<1/2\). [Exact program](../data/n7/allN/hier/r35/family.py) · [All cells and controls](../data/n7/allN/hier/r35/family.log)

The release program orders affine forms lexicographically by slope and intercept, and both its equality and strict-order comparisons register the crossing when slopes differ. Sorting, maxima and tie checks follow a finite comparison trace. Above its largest registered crossing the same branches are taken, including every compared equality. Identical polynomials agree identically. The check that the maximum has coefficients \((1,0)\) is symbolic. Hence the method proves its advertised \(\chi>3\); its later numerical evaluations provide controls. The code does not claim to settle the endpoint. The value 3 is the sharp lower boundary, and equality at the boundary works. The two damaged-height controls discriminate ultrametric and cut failure. There is no conflict with the paper’s chamber theorems, their Lean hypotheses, or a result about actual \(K\)-solutions.

**Remark 9.2 and Table 3.** Replacing the force exponent by \(\rho\) gives body score \((\rho-2)(\zeta+\omega)/2-u_t-u_l\), so for \(\rho<2\) the triangle estimate points the same way as the maximum inequality. Nurowski’s Theorems 1.10 and 1.11 give the two regular polygons at equal masses and the smooth local one-dimensional families near a collision-free member when all masses vary. At an excluded angle the polygons coincide pairwise and the polynomial pair force vanishes at contact. These are different force laws. Table 3 correctly locates the Newtonian coefficient/parity and the use of all body pairs. The chamber examples show failure without a suitable mass hypothesis and do not determine an optimal constant. For the free \(\theta\) row the modified origin score includes \(-v(\theta)\). Scaling \(X,Y\) by \(a\), \(P\) by \(a^{-1}\) and \(\theta\) by \(a^{-3}\) adds \(v(a)\) to every modified score. The extra relation term is \(-\sigma_Ov(\theta)=(N/3)v(\theta)\). [Nurowski, Theorems 1.10 and 1.11](https://arxiv.org/html/2610.04136v1)

## Changes since the ninth read

I compared the two TeX files and the two bibliographies directly. These are current line numbers. Each row covers all sentences in the indicated change hunks. The two zero-context diffs preserve the complete old and new text. [Paper diff](../data/n7/allN/hier/r35/R34-paper.diff) · [Bibliography diff](../data/n7/allN/hier/r35/R34-references.diff)

| Current lines | Assessment of the change |
| --- | --- |
| 64–67 | “Bounded above” and arbitrarily large valuation of one mutual-distance square follow from Corollary 6.3 and Proposition 7.1. The absolute scale of the separate complex coordinates is immaterial to their product. |
| 127, 134 | The Okolo public record verifies restricted access. No readable theorem or mass hypothesis accompanies the title. “We could read its title only” is accurate about the mathematical contents. The adjoining statement about the entire works of Xia and Moczurad–Zgliczyński is broader than the intended counting claim (A10). |
| 184–190 | The algebraically closed field, unique nonzero slice, polynomial counts, degrees, intersection inequality and finite-point interpretation all hold. B1 adds the corrigendum. |
| 816–817, 902–906 | Every **real** valuation is available for a nonconstant component function. The closed set in the torus is the restriction of the base-changed closure, and the open set meets every surviving component. Both revisions are correct. |
| 943, 949–963 | The new row and the entire family in Remark 9.1 check symbolically, including the treatment of the infinite origin height. Parts (c) and (d) fail with distinct weights alone. No lifting of that datum is asserted. |
| 974–978 | Equal-mass polygons and local persistence with perturbed positive masses match Nurowski 1.10–1.11. The coinciding vertices are in the excluded equal-mass members. |
| 1026, 1029–1032, 1045–1046 | The Linux outputs and flags support six acceptances per list and rejection of sandbox startup. The SHA file is the input reference. The macOS and mutation runs have the evidentiary status given in B3. |
| 1105–1123 | Three **types** of exact computation is correct; the README runs four executable commands because multiple programs repeat the second computation and the R34 program also performs the first. Finite heights can be represented by binary refinements. Exchange symmetry, counts, seed, version and tolerances agree. Specify the search domain and the graph tolerance (A2, B2). |
| 1128–1132, 1140–1142, 1150, 1153–1155 | The caption and five-body row changes correct the earlier count of candidates. Rounded bounds and maxima agree. The attribution to R34 is accurate. Its integer code executes tolerance predicates on recorded decimals; exact membership of \(\mathcal E^*\) differs on 794 records (A2). |
| 1162–1168 | Both controls have matching programs and outputs. The exact three-body assertion includes origin strata. The four-body floating-point control supplies the cycle up to exchanging the colour names. |
| 1171–1182 | The top pair must be the two heaviest bodies of the intersection of its nodes when weights are distinct: every other internal pair has both heights at least as high, and strictly smaller weight sum would beat the putative maximum. Hierarchies, unordered/ordered counts, all-six-body incidence, and R30/R34 provenance hold. Attribute the two larger experiments individually (B2). |
| 1184, 1187, 1193–1195 | The chamber vectors, order types, integer feasibility decision, repeated-weight control and the three implementations match the records. R32 read a draft, as the revised sentence says. |
| 1197–1203 | All formulas have rational affine coefficients, and all crossings needed on the comparison trace were recorded. R34’s solver output contains precisely the \(\chi=1000\) member, including \(\eta_3=+\infty\). The subsequent family and program are attributed separately. |
| 1239–1241, 1244–1247, 1249 | Three statement files and nine prior sessions is the right inventory. The archive supports the program attributions. Five reports give no model name. The listed commercial variants are the author's configuration (A8). |
| 1266–1282, 1288–1292 | R34's substantive findings on tree representatives, as-run tolerance, hierarchy source, slice citation and the exact solver are attested in its report. R33 had the revised passages as its remit. Scope the statement about which changes had been read to the nine archived reports (A9). |
| references.bib 184, 191 | EGA IV.3 has pp. 5–255. I retrieved both Tomar six-body PDFs. The relevant §2.1, §2.3, §4.1 and §9.1 references agree at Zenodo v5 and Hexagon v1. The title of the page and the approved theorem scope agree. |

## Formal statements and gate

| Frozen file | Theorems in its comparison, in order | Mathematical reading |
| --- | --- | --- |
| Challenge.lean · 280 lines | lemmaB, lemmaC, degree_two, exists_cycle, cycle_relation, collision_bound, chamber_nonempty, ex2_spec, ex3_spec, ex3c_spec, ex3m_spec, ex4_cycle | Prefix nonvanishing, node-cycle exclusion, both parts of (a), the simple-cycle identity and nonzero coefficient, and the pair bound. The chamber existence statement and five example declarations make six tests. The extra three-body examples are described in the Section 10 prose and named in the Lean README. |
| ChallengeA.lean · 57 lines | lemmaA, solution_bound | IsSolution includes symmetric \(P\), all three equations and nonzero masses in the theorem. The weights of a solution over any field with the specified additive valuation satisfy all cuts. The pair bound concerns \(v((X_t-X_l)(Y_t-Y_l))\) itself. The individual cut identities are outside the challenge statements. |
| ChallengeB.lean · 103 lines | lemmaB_sign, lemmaC_alt, cycle_alt_bodies, alt_relation, cycle_alt, psi_star_bound, ex2_alt, ex4_alt | The positive product gives the sign, IsAltSeq matches equal heights, and the two cycle-to-alternation implications use nodes. alt_relation asserts the occurrence of an origin edge, the relation and \(N\ne0\). psi_star_bound gives the inequality. The two examples assert the particular sequences. |

I matched each configuration list to the declarations and solution module. The nine trusted entries pass SHA-256 verification. All three Table 5 values match the files and the Linux version record.

| File | SHA-256 |
| --- | --- |
| Challenge.lean | 98bc0a4f29f32f26484136717c7ac15b05efd387e3344a048fbbe0b0cf48feec |
| ChallengeA.lean | eb0bceb664c95a884e4f8a5453062c77279ff8fe9db45cd1d9beb41f1c697b22 |
| ChallengeB.lean | 1879a2be79d0963d85317940e82ff2d98ca3a3421ea56a2b51000d615a971038 |

The symbols in the Lean README correspond to the paper, including Chamber, IsUltra, node, Datum’s edge, maximum and cut predicates, IsSolution, weights, psiPair, topPairs, IsCycle, IsAltSeq, cycN, inc and cycQ. I checked the eight stated encoding differences. Natural-number padding, the separate \(O=n\), finite body heights, guards on infinite origin positions, attained maximum as parameter, three injectivity/disjointness fields, prefix sums and the sign test give the claimed meanings. The valued-field generality, the combined (b,c) and the chamber-free (a) are genuine. The stored diagonal influences only trivial symmetry checks. The padded \(n<2\) convention reads entries 0 and 1. The two-body examples specialize \(u\), and the four-body example asserts the displayed cycle and ultrametrics. Lemma 3.2 is not a frozen theorem. The finite-set assertion of 6.2(d), Lemmas 2.1–2.4, Proposition 7.1, Lemma 8.1 and the three finiteness deductions have only the printed proof here.

I searched the 11 DirectRoute modules and all three Solution files for the whole tokens sorry, admit, sorryAx, axiom, unsafe, native_decide and implemented_by. There were zero hits including comments. The same test detects the 12 intentional sorry bodies in Challenge and the synthetic seven-token control. Each of the three configs permits exactly propext, Quot.sound and Classical.choice. lean_gate.sh checks the supplied manifest, the named configurations, module-shadow checks and exit status of each comparator. With these nine pinned files it selects all three lists. Its final success line starts with GATE PASS. --local passes --inadvisably-no-sandbox and --final adds --paranoid. The manifest is the reader's trust input. [Source and manifest checks](../data/n7/allN/hier/r35/details.log) · [All nine digests](../data/n7/allN/hier/r35/runs/trusted.log)

In data/n7/allN/hier/lean the setup transcript identifies Lean 4.36.0 on x86-64 Linux. Mathlib is pinned through the v4.36.0 lakefile and lockfile. The build log exits zero. The namespace test and all three sandboxed comparator invocations fail to start bubblewrap. Each of the three unsandboxed paranoid invocations then logs acceptance by leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron and the default kernel, and exits zero. The proof/source hashes in versions.json match all the corresponding release files; comparator-stage1.json is a historical auxiliary entry outside the three final lists. These log files show component commands; the final wrapper transcript and the other historical runs are not among them. [Linux run summary](../data/n7/allN/hier/lean/leangate3_cmp_za6lxQYhmPdbSfiCnWljhkD9/summary.json)

## Floating-point searches and exact computations

I independently decoded the decimal strings into integer units of \(10^{-5}\), doubled the score units to retain half-increments, and checked every triangle and cut. I built threshold balls from distances to a vertex without the binary tree indices, traversed each observed two-regular component and recomputed \(N,q\). Each point has one numerical cycle. The largest triangle gap is zero, largest cut gap \(0.000015\), and largest absolute relation residual \(0.00002\). A two-body control recovers its known cycle; changing one height makes the test fail. The sets of heights reconstructed from each parts file agree with the summary points, and sums of the per-part LP and undecided counts agree with the summaries. [Program](../data/n7/allN/hier/r35/points.py) · [Full command headers and calculations](../data/n7/allN/hier/r35/points.log)

| Table 6 run and weights | Tree pairs and search settings from the first log line | Distinct points | Largest reconstructed \(\Psi^*\) | Unrounded bound | Records where tolerance adds top edges |
| --- | --- | ---: | ---: | ---: | ---: |
| HP · 0, 1, 12, 150, 1900 | 446,985 representatives, symmetry, \(R=5\), relative | 203 | 2424.33334 | 6189 | 122 |
| GP · 0, 1, 2.37, 4.91, 8.53 | 446,985 representatives, symmetry, \(R=3\), relative | 30 | 5.52 | 50.43 | 26 |
| WP · 0, 1, 52, 2700, 140000 | 446,985 representatives, symmetry, \(R=5\), relative | 204 | 184831 | 428259 | 165 |
| BL · 0, 1, 45, 2000, 89000, 3920000 | 100,000 ordered, seed 29, no threshold, absolute | 1,589 | 2613302.66667 | 44121506/3 | 267 |
| BP · same as BL | 500,000 ordered, seed 29, \(R=5\), absolute | 189 | 7749636 | 44121506/3 | 148 |
| AP · 0, 1, 12, 150, 1900, 24000 | 300,000 ordered, seed 29, \(R=5\), absolute | 108 | 31837.33334 | 286693/3 | 66 |

The five-body tree count is \(9!!=945\). The symmetric loop visits \(945\cdot946/2=446{,}985\) representatives of \(945^2=893{,}025\) ordered pairs. Its three runs have 945 different completed first-tree entries each. The archived source hash begins 6a9bbfdf. The gap test uses \(10^{-7}(1+|\max\Phi|)\). For six bodies \(11!!=10{,}395\) and its square is 108,056,025. Sampling is without replacement by ordered pair, and the three percentages round to 0.09%, 0.46% and 0.28%. All specify --abs-tol 0.001 and seed 29. This source hash begins 09969dd4. Both versions use the released fixedu_enum.py with digest beginning 4fe2f9b9. All six log commands, including their archival, temporary output paths and time budgets, are transcribed in points.log. The large clock times in the original logs belong to the original runs.

For HP, GP, WP, BL/BP and AP the respective strict upper endpoints for admissible chamber \(\tau\) are \(11,362/491,1373/27,3831/89,11\). Thus WP is in \(W_5(50)\); BL/BP are in \(W_6(43)\) but outside \(W_6(72)\). The estimates actually used by the two proofs yield the sufficient bounds 27 and 43 for six bodies, and all three dagger annotations are right. Each observed maximum is below the unrounded bound.

**Controls.** The seven archived R34 threshold logs and my seven replays show four distinct points each for \(-40,-20,-1.5\) and zero for \(-0.9,0,10,1000\). My separate rational linear-arithmetic model considers all 16 pairs of origin strata for three bodies. Each colour permits at most one infinite origin height by the finite body triangles. For \(u=(0,1,30)\) an all-finite datum with maximum \(-1\) is satisfiable and every stratum with maximum different from \(-1\) is unsatisfiable. For the R29 control see lp4ctl.out, lines 18–26, and the three comparison blocks following it. They exhibit the four-edge zero-\(N\) set at \((0,1,2,3)\), with colours exchangeable, and no such numerical failure at \((0,1,2.37,4.91),(0,1,30,900),(0,1,4,16)\). Indeed the dot product for that *specific* \(q\) is nonzero at each comparison vector. The R34 exact witness at 1000 has the heights in the new family. [Independent three-body control](../data/n7/allN/hier/r35/three.log) · [Archived R29 control](../data/n7/allN/hier/r29/lp4ctl.out)

**Independent enumeration.** I generated chains of strict coarsenings of labelled set partitions, allowing simultaneous mergers. Forgetting rank while retaining each pair’s cluster gives the unranked hierarchies. For the rank tests, a pair dominated in both heights by a pair of smaller weight sum cannot attain the maximum. I enumerated simple cycles of the remaining rank graph including parallel edges. Any edge-distinct closed alternating walk contains such a cycle. To test a candidate, translate one colour so the common maximal score is zero; after negating the other colour, the bounds and required equalities are difference inequalities. For \(k\) level variables, scaling integer bounds by \(k+1\) and representing strict order by a gap of one preserves feasibility: a simple directed circuit has at most \(k\) strict comparisons. An integer negative-cycle test then decides the original real system. The unranked test instead selects the two heaviest bodies in each node intersection and compares signed incidence at every body. [Independent C++ source](../data/n7/allN/hier/r35/count.cpp) · [Counts](../data/n7/allN/hier/r35/count.log)

| Bodies | Ranked types | Unordered ranked pairs | Feasible cycles at the stated chamber vector | Hierarchies | Balanced heaviest-pair cycles, unordered |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 1 | 1 | 0 | 1 | 0 |
| 3 | 4 | 10 | 0 | 4 | 0 |
| 4 | 32 | 528 | 0 | 26 | 0 |
| 5 | 436 | 95,266 | 0 | 236 | 0 |
| 6 | 9,012 | 40,612,578 | 0 | 2,752 | 96 |

At six bodies 144 ranked cycles pass the necessary balance check before height feasibility rules them out. All 96 unranked instances use six bodies, and none has equal colour hierarchies, giving 192 with colour order retained. The repeated-weight positive control yields 78 two-edge and four four-edge feasible cycles, including Example 5.4. The latter is a control for the zero ranked results; the 96 six-body instances control the zero small unranked counts. This is an independent check at the tested sizes and vectors. The general proof is in the paper.

## Release, instructions and publication checks

### File and directory ledger

The inventory covers the entire staged payload. FILES.sha256 lists 167 other files. Each SHA-256 matches the working file, and I independently recomputed each Git blob ID, including that of the manifest, against the staged index. The checkout is an unborn release-draft branch with zero reachable commits. Every one of 168 paths has stage status A; the release had no extra tracked modification, untracked or ignored file. The remote is the expected public HTTPS GitHub path, with no embedded credentials. The payload is 2,884,934 bytes. Its largest file is main.pdf (465,784 bytes). There is ample margin below ordinary hosting limits. [Full inventory](../data/n7/allN/hier/r35/files-opened.txt) · [Audit log](../data/n7/allN/hier/r35/audit.log)

| Directory and file count | Check performed |
| --- | --- |
| Root · 6 | Read the README in order, both licences, CFF, ignore rules and integrity manifest. Compared the index and remote to the paper. The existing ignore rules cover paper intermediates, the Lean cache, Python artifacts and two compiled checks. B4 adds the third executable. |
| paper/alln · 3 | Read complete source and bibliography, inspected every released PDF page, checked destinations and rebuilt in the copy. |
| lean/direct-route · 14 | Read the three statement files, three solution entry modules, configs, manifest, Lake file, toolchain, digest file and README. Name, type, scope and digest crosswalk above. |
| lean/direct-route/DirectRoute · 11 | Inspected imports, definitions and module roles and scanned all proof text for the seven specified tokens. Regenerated the files written by the Python templates in the copy and compared the resulting bytes. This was a source check, with the kernel evidence supplied by the archived runs. |
| scripts/allN · 9 | Checked the gate argument and manifest flow, the three source generators, the finite tree/LP representation, cut and cycle rechecks, as-run version differences, threshold and sampling code, and the complete exact-family program. |
| data/n7/allN/hier/lean · 11 | Opened setup, build, namespace probe, successful and failed comparisons, summary and versions. Verified success/failure codes, machine architecture and hashes. A6 covers the hostname. |
| data/n7/allN/hier/nk · 23 | Decoded all six sets of points, parts and command logs, both summaries, both versions files, and the five-body as-run source. Compared per-part totals, point sets, thresholds, samples, tolerances and independent measurements. |
| data/n7/allN/hier/r29 · 24 | Read the batch parameter lists, common/LP, cut-generator and three-body program roles; cross-checked the relevant controls against their outputs. The four-body record explicitly shows the four-edge witness and reports the other vectors. Origin-stratum results explain R29’s correction. |
| data/n7/allN/hier/r30 · 10 | Read the hierarchy, cycle, LP, certificate and sampling programs and their file dependencies. Reran the documented three small enumerations. Independently recovered all six-body survivors and reran the downstream programs, including both certificate passes. A11 gives the print bug. |
| data/n7/allN/hier/r31 · 2 | Replayed the pattern search and matched all result lines against the archived output and the report’s \(n=8\)–13 range, 653,600 placements and positive outside-chamber control. This is a pattern search, distinct from the R30 heaviest-pair census. |
| data/n7/allN/hier/r32 · 2 | Checked the C++17 rank enumeration and adjacent expected results, and replayed it. |
| data/n7/allN/hier/r33 · 4 | Checked the local example code/output and C++20 rank computation/output. Replayed both. The local examples agree on their three mathematical lines, and all seven rank-count lines agree. |
| data/n7/allN/hier/r34 · 26 | Checked the previous inventory, digests, document and numerical logs, seven thresholds, exact constraints, rank and hierarchy enumeration, and point-recomputation code. Their numbers refer to that earlier snapshot. Replayed the C++ evidence and independently rederived the current numerical and exact claims. |
| docs · 14 | Reviewed the README, four archived prompts, six referee reports and three formal-statement reports. Checked local Markdown links, line anchors, rendered-column delimiters, model attribution and substantive verdicts. |
| docs/as-read · 9 | Identified the R29, R30 and R31 note/brief snapshots and the three TeX/BibTeX snapshot pairs. Read the R34 diff, checked the R32/R33 repair/provenance and matched the third statement review’s line citations to the R33 snapshot. Historical file and commit references are scoped by the archive README. |

### Root README replay

The working Python was 3.13 in an isolated r35 environment; the documented numerical dependencies were NumPy 2.5.5 and highspy 1.16.0. The default system Python lacked those imports, which the README correctly says are needed. The cut check alone ran with only standard-library imports. The jobs were run in sequence. The small search is one invocation with its documented default pool of four workers. The longest root command took 40.08 seconds. The maximum sampled process-group RSS of these commands was below 160 MB. [Timing and status ledger](../data/n7/allN/hier/r35/readme-runs.log)

| README line | Result |
| --- | --- |
| 55 · paper build | The literal cd and latexmk invocation succeeded. All references resolved on the final pass. |
| 62–66 · Lean setup, build, gate | Directory and reference arguments check. The cache and build were explicitly excluded, so the live gate was not run. Its comparator and digest behavior is covered above. |
| 84 · statement digests | All three match the paper and TRUSTED.sha256. The independent check of each of the nine reference entries also passed. |
| 92 · recorded-point cut check | The literal globs selected the six intended files. All 2,323 points passed at the recheck tolerance. |
| 97 · recorded cycles | Same six files. Reported one basis cycle per point, no failed relation at the script’s threshold, worst residual about \(2\cdot10^{-5}\). |
| 98 · small four-body search | 11,025 tree pairs, 1,731,527 LPs, zero undecided, 28 found and six distinct points, largest observed maximum 747. |
| 119–121 · compile and run | The R32 and R33 outputs agree with lines 2–8 of their respective reference files. The entire R34 program output agrees with the first eleven lines of its log. The stored timing/compiler lines explain the two literal file-comparison differences. |
| 122 · exact family | Reports the bound 3, all 30 cuts, the four edges, \(N=0\), the stated \(q\), two numerical cross-checks and the damaged-height controls. |

The additional R30 full Python census reached 96 survivors by first-tree index 2400 but could not finish within my 855-second cutoff. The shorter preliminary attempt also stopped before completion. Neither partial log is a final count. The independent integer program completed the full census in 2.71 seconds. I converted its 96 unordered witnesses to both colour orders, reconstructed their cluster labels in R30’s indexing, and checked each with the archived cycle functions. The unchanged downstream R30 LPs found 0/192 feasible at the tested chamber vectors and 192/192 for equal weights. The exact fallback validated all 192 at the six-body chamber point; the hard-coded total in cert6b.py then reported 300/192. The proposed line prints 192/192 on the same data. The historical 108/84 split can depend on the LP supports. The number of exact certificates in the combined run is reproducible. [Replay status](../data/n7/allN/hier/r35/r30-replay.log) · [Witness conversion](../data/n7/allN/hier/r35/recover_r30.py) · [Original final line](../data/n7/allN/hier/r35/runs/recovered-r30-cert6b.log) · [Corrected trial](../data/n7/allN/hier/r35/runs/fixed-r30-cert6b.log)

### What the nine reports actually reviewed

| Session | Evidence and limit |
| --- | --- |
| R29 | Identifies the working note at bbc262f, Sections 1, 2 and 3a plus selected material. Accepts the main propositions with fixes. It found a false computational assertion for four-body origin strata and an implementation error; the current cherry test checks against both endpoints. The report also identifies earlier background it read. |
| R30 | Describes a read of the second brief, the constituent bound omissions, a small-\(n\) clarification, hierarchy census, exact certificates and randomized tests at 7 and 8. It explicitly did not do a live literature search and does not specify a development commit. |
| R31 | Names the brief at 7421729, assesses the former corner argument and the scheme-theoretic step, finds the two six-body preprints and the two all-\(n\) claims, and tests selected cycles at 8–13. Its four-body control shows why its requested qualifier on the auxiliary six-body claim matters. It discloses seeing a prior verdict in a commit subject. |
| Statement review 1 | Compares the initial Challenge with the brief. Its “freeze as is” verdict accompanies comment edits and two suggested supplemental examples. The final test list includes those examples. It explicitly excluded the proof files. |
| Statement review 2 | Compares ChallengeA with the brief. Checks the cut statement over any indicated valued field and supplies the two-body Hahn witness with weights \((3,4)\). It excluded the implementations and recommends freezing. |
| Statement review 3 | Compares ChallengeB and imported definitions from Challenge with the paper. Explicitly identifies the inequality-only scope of (d) and recommends freezing. Its eleven line links correspond to R33-paper.tex. |
| R32 | Names 66ca227. Assigned printed arguments, states a specific invalid invocation of Lemma 3.2(a) in the earlier proof of (d), and writes the exact height-order program. It lists two challenge files for the formal-statement portion. |
| R33 | Names c379106 and the diff from 66ca227. Reviews the repair and revisions, reproduces the rank search independently, and identifies remaining scope and wording issues. |
| R34 | A release-oriented full read of the pre-correction snapshot, with a prior 125-file inventory. Its report documents the five-body symmetry/tolerance, R30 attribution, exact solver witness and other requests. Its 19 distinct links to its own artifacts really do point to archived copies. Its historical G6 wording about constructible sets needs the archive note in B1. |

The configuration is the only source here for the Qwen4 Max and GPT-6.2 Sol assignments and the claimed effort setting. R32, R33 and R34 identify GPT-6 without a finer serving variant; statement review 3 also identifies GPT-6. R29, R30, R31 and statement reviews 1 and 2 give no model identifier. The paper correctly calls these language-model reads and states the peer-review status. Its stronger summary of what the readers found should distinguish R29’s substantive ancillary error (A9).

### Paths, publication scan, PDF and licences

**Paths.** All current paper, root README, Lean README and CFF entry points resolve with the documented working directories. Bare names such as ChallengeA.lean and nk_cycle_check.py are located in the directories stated in the paper; run labels such as nk5psi_*/HP denote filename stems with three suffixes. Historical development paths and commits intentionally omitted from the release are listed as such in docs/README.md. Its two brief aliases exist. The historical R31 Markdown target is missing and the third Lean review’s eleven fragments land at unrelated current lines. A8 fixes both. The as-read TeX sources refer to references.bib under the original build name; the corresponding R32-, R33- and R34-prefixed bibliographies sit alongside them. The R30 pickles are generated intermediates. The documented recipe order is correct: cert6b also needs cert6_fails.pkl produced by cert6, and d4n4b reads its sibling source d4n4.py.

**External links.** I resolved the current PDF’s seven external URI annotations, the three READMEs’ external links and the CFF address. The GitHub release URL returned the expected prepublication 404. All other current reader-facing endpoints, including the Tomar DOI, Hexagon PDFs, Stacks and restricted Okolo landing page, opened by ordinary HTTP GET. I also checked the extra article, library, software and archive URLs found in the historical text. The two ScienceDirect articles and the Academia mirror rejected direct automated requests; the search tool returned the relevant primary text or record. The log distinguishes HTTP status and document type. A DOI prefix split across a PDF text line is not its hyperlink destination. [HTTP ledger](../data/n7/allN/hier/r35/links.tsv) · [Software and log links](../data/n7/allN/hier/r35/extra-links.tsv)

**PDF.** I inspected all 22 rendered pages and all six tables. Pages 1–4 contain the abstract, Table 1 and main statements. Pages 5–12 carry the normalization, cuts, Table 2, and combinatorial proofs. Pages 13–15 carry generic masses, the family and Table 3. Table 4 on p. 16, Table 5 on p. 17 and Table 6 on p. 19 all fit their columns. The long six-body vectors and digest strings are legible without overlap. Pages 20–22 contain the problems, disclosures and bibliography. All 351 internal GoTo actions point to existing named destinations. There are 138 named destinations and seven external annotation fragments, including two segments for the same DOI. Source references and citation keys all resolve. The delivered and rebuilt PDFs have identical extracted layout text. The final release-source build has two underfull caption lines, no overfull box or unresolved citation. The PDF metadata records pdfTeX, hyperref and the build time; its author, title and subject metadata fields are empty. No JavaScript or attached form appeared. Rendered pages · [Build log](../data/n7/allN/hier/r35/runs/paper.log)

**Publication scan.** I scanned all listed text, all 23 gzip payloads after decompression, their original-filename fields, the PDF’s text, document information and metadata, and paths in the index. I tested patterns for e-mail addresses, absolute and home-relative machine paths, OS host identifiers, local addresses, credential assignments, private-key markers, bearer and provider token formats, private-service names and internal or disparaging language. Synthetic positives exercise each search family. The archived R34 scanner contains a deliberately fictitious address, a test-user path and a key *marker*. The container hostname is a real hit, as are the old home-relative layout instructions in A6. The /root/.elan and /tmp paths are generic execution locations. Three opaque cmp_ run labels occur in historical directory names; I found no evidence that they grant access. The /users/ URL for Payne is public. Source “todo” hits are ordinary work-list variables. The gzip header filenames are staging basenames ending in .gz.part. Tool/vendor names in the authorship history are public attributions. I found no actual private key, account token, personal e-mail, private IP or disparaging aside in the scan. The accepted R29 byline and the author's planned README contact are outside the findings. [Audited hits](../data/n7/allN/hier/r35/scan-hits.tsv) · [Additional patterns and controls](../data/n7/allN/hier/r35/closeout.log)

**Licence and citation.** LICENSE contains the MIT grant for software. LICENSE-CC-BY-4.0 contains Attribution 4.0 International. CITATION.cff parses as YAML and validates against the official CFF 1.2.0 schema. The top-level title identifies the software repository; the preferred unpublished-paper citation matches the exact paper title, sole author and year. The affiliation and HTTPS repository address agree with the manuscript and Git remote. A7 records the proposed data allocation and both SPDX identifiers. The release can implement the author's licence choices without changing either standard licence text. [CFF schema](https://raw.githubusercontent.com/citation-file-format/citation-file-format/1.2.0/schema.json) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/legalcode.en)

## Literature checked on 18 November 2026

### Xia from the supplied full text

I read the supplied twelve-page publisher PDF, printed pp. 168–179, and inspected page images for the delicate numbers. Its SHA-256 is 0360f3caa639de646c57c9fae259138bc6e3bdb752f39a85d3219fb5d1165302. This is distinct from relying on the abstract. Supplied Xia paper · [Publisher record](https://doi.org/10.1016/0022-0396(91)90137-X)

- **Which configurations.** Page 168 puts the positions in the Euclidean plane. Pages 169–170 quotient by scaling and \(SO(2)\) and then fix the multiplier. Labels are retained; the two triangular orientations contribute two classes at three bodies. The final remark on pp. 178–179 suggests a future spatial extension. Thus Xia’s count is planar and uses direct similarities. The paper under review also permits reflections, which preserves finiteness but can change the exact count.
- **Which masses.** Section 2 treats the addition of two small bodies. Proposition 1 on p. 171 gives continuation when their limiting equilibria are distinct. Pages 172–174 resolve the coincident limit and describe exhaustion of the possibilities. Section 3 iterates by first keeping one new mass zero and continuing the other. Sections 3 and 5, especially pp. 176–178, explicitly describe starting with two or three large masses and adding the remaining \(n-2\) or \(n-3\) at successively smaller scales. This produces neighbourhoods in the full positive mass space, with the large masses free to vary. The result is about some open sets. It supplies neither a formula defining a Zariski-exceptional set nor a count on its complement.
- **What is exact.** The all-\(n\) counting conclusion is in the prose of §3, p. 177, following the continuation argument. For \(n\ge4\) it gives two ordinary open sets with different counts and nondegenerate configurations. These are total counts on those sets. Table I illustrates \(4\le n\le10\). The explicitly headed Theorem in §4, p. 178, is instead a statement about the positive \((n-1)\)-dimensional Hausdorff measure of the degeneracy locus. For this reason a statement that Xia says nothing away from the counting neighbourhoods is too broad. A10 corrects the unit of counting and that attribution.
- **A numerical caveat in the 1991 source.** On p. 176 Xia prints 36 immediately before counts of 24 saddles and 14 minima. Those add to 38, the number in Table I. There are also transcription or arithmetic discrepancies at larger \(n\). Using the local continuation rules on pp. 175–176, a state with \(a\) minima and \(b\) saddles produces \(a\) descendants of type \((a+1,b+2)\) and \(b\) of type \((a,b+1)\). Starting from \((2,3)\) at two primaries gives 34, 294, 3,096, **38,520**, **553,680** for four through eight bodies. The source prints 38,250 and 5,536,800 for the latter two. The alternative three-large-mass start gives 38, 374, 4,512, 64,248 and 1,051,440, consistent with those five cells. The release's Xia row contains none of these numbers. The distinction matters if numerical examples are added later. [Exact integer recurrence](../data/n7/allN/hier/r35/xia_counts.py) · [Results](../data/n7/allN/hier/r35/xia-counts.log)

Before the file was supplied I tried the ScienceDirect open archive and PDF (403), the Elsevier API (no authorized full text), Xia’s Northwestern page (three different linked preprints), the OpenAlex and Semantic Scholar records (publisher DOI only), INIST and university library catalogues (metadata or holdings), ADS (no PDF) and an Internet Archive article/journal search (zero matching 1991 scans). Known DOI and four-/six-body papers were positive search controls. The supplied PDF resolved this limitation. [Author’s page](https://sites.math.northwestern.edu/~xia/) · [OpenAlex record](https://openalex.org/W1965505736) · [Request log](../data/n7/allN/hier/r35/links.tsv)

### Table 1 in its printed order

| Entry | Finding against the primary source |
| --- | --- |
| 4 · Hampton and Moeckel | Published finiteness of planar relative equilibria for all positive masses. The scope in the introduction agrees. [Inventiones paper](https://doi.org/10.1007/s00222-005-0461-0) |
| 5 · Albouy and Kaloshin | Theorems 2 and 6 give the five-body result outside the specified mass subvariety of codimension two. The complex system, the signed-distance example on p. 543 and in Remark 8, Lemma 1 on images and Rule 1c on p. 546 support the attributions in the paper. [Annals article](https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p10-p.pdf) |
| 5 · Jensen and Leykin | The published tropical-prevariety computation proves the generic five-body case. The six-body computation does not supply the missing unrestricted result. The valued-mass comparison in the introduction is appropriate. [Journal](https://doi.org/10.56994/JXM.001.002.006) · [§§3–4](https://arxiv.org/html/2301.02305v2) |
| 5 · Tomar, Chen–Tong, Liu–Liu | All three are October 2026 preprints asserting finiteness at every positive mass vector. The current title of Tomar v2 differs from its first title. The survey suitably identifies the sources as preprints. [Tomar v2](https://arxiv.org/abs/2610.13100v2) · [Chen–Tong](https://arxiv.org/abs/2610.16107) · [Liu–Liu](https://arxiv.org/abs/2610.28168) |
| 6 · Tomar | Zenodo v5 and the Hexagon copy give Theorem 1.1 for positive masses where a nonzero integer polynomial does not vanish. The paper reports its own diagram enumeration, computer algebra and a Lean formalization of that theorem. The slice/identity/tree citations have the same section numbers in the two copies. This is attribution to Tomar’s reported formalization. [Zenodo v5](https://doi.org/10.5281/zenodo.23720035) · [Author copy](https://hexagonmath.org/2611.00377v1) |
| 6 · Chen and Tong | Part I, Corollary 1.2 gives finiteness off the indicated exceptional mass set. It uses the Chang–Chen diagram classification and further certificates. Part II is proposed for the remaining masses. The source PDF and landing page have the two titles reported in the bibliography. [Paper](https://arxiv.org/pdf/2610.23329v1) · [Metadata](https://arxiv.org/abs/2610.23329) |
| 6 · Dias and Pan | Theorem 7.10 is about cross configurations, with four bodies on the symmetry line and \(m_5=m_6\), off a proper closed set in the reduced mass space. [Paper](https://arxiv.org/pdf/1811.08681) |
| 5–7 · Moczurad and Zgliczyński, equal | Complete computational planar listings with equal masses at 5, 6 and 7. [2019 article](https://doi.org/10.1007/s10569-019-9920-6) |
| 4–7 · Moczurad and Zgliczyński, near equal | The paper with “spatial” in its title also gives the planar counts for 4–7 throughout a usual neighbourhood of equal masses. [2020 article](https://doi.org/10.1007/s10569-020-09993-1) · [Authors’ abstract](https://arxiv.org/abs/2006.06768) |
| all · Moeckel | Theorem 3 is for affine dimension \(n-2\) off a proper projective mass subvariety. In this table’s \(n\ge4\) range, only \(n=4\) gives dimension two. [Moeckel, Theorem 3](https://www-users.cse.umn.edu/~rmoeckel/research/DziobekAMSLaTeX.pdf) |
| all · Xia | All-\(n\) planar ordinary-open-set result confirmed from the supplied publication. Distinguish direct similarity if reporting numbers (A10). Xia, §§2–5 |
| all · Tibboel | The author’s withdrawal identifies the incorrect Lemma 2.7 and its effect on the main argument. It is an earlier claim, not a verified proof. [arXiv withdrawal](https://arxiv.org/abs/1305.1728) |
| all · Okolo | The public API gives the title, author, date, DOI, preprint type and restricted-access status. Its description states that the abstract and contents are hidden. I could not determine a mass hypothesis or assess the argument. The author’s public publication list independently identifies the claim. [Zenodo record](https://zenodo.org/records/23576138) · [Public metadata](https://zenodo.org/api/records/23576138) |

### Priority and counterexamples

On 18 November I searched arXiv, Zenodo, Hexagon, publisher records and broader scholarly search under “generic finiteness”, “seven bodies”, “planar relative equilibria”, “all positive masses”, “valuation–lattice”, “continuum”, “degenerate central configurations” and combinations with the Newtonian force and exceptional masses. The searches returned both six-body preprints, the seven-body equal-mass listings, the general Dziobek result, the withdrawn claim and the restricted record. A current project describing open bridges in a proposed general proof does not claim to discharge them. Natrup–Wang–Wang bound the **nondegenerate** solutions, while Dias’s general homogeneous-potential work requires dimension \(n-2\). A secondary attribution of almost-everywhere nondegeneracy to Palmore is not substantiated by the primary sources I inspected: Smale explicitly asks about measure zero, and Xia’s §4 establishes a positive lower-dimensional measure, which supplies no measure-zero or finiteness theorem for generic masses. I found no accessible prior proof for all planar configurations at Zariski-generic masses for any \(n\ge7\). This supports the modest priority wording “we know no earlier proof.” [Natrup–Wang–Wang](https://arxiv.org/abs/2502.20228) · [Dias](https://arxiv.org/abs/2601.07962) · [Smale, Problem 6](https://www.fim.uni-passau.de/fileadmin/dokumente/fakultaeten/fim/lehrstuhl/muller/SmaleProblems1998.pdf) · [Open-bridge project](https://thalens.org/problems/smale6/)

The continuum search recovered Roberts at constant masses proportional to \((1,1,1,1,-1/4)\), its positive-mass signed-root counterpart, varying-mass constructions and examples for other forces. The first two lie over special ratios with equal valuations up to common scaling; a family varying the mass vector does not by itself give an infinite fibre. Nurowski’s exponents are different. Zero masses are excluded from Theorem 1.3. For Theorem 1.2 a single exceptional vector is expressly allowed. I found no fixed-mass continuum in the stipulated Hahn chamber and no Zariski-dense bad locus for the Newtonian complex system. [Roberts](https://mathcs.holycross.edu/~groberts/Papers/continuum.pdf) · [Albouy–Kaloshin](https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p10-p.pdf) · [Tomar](https://hexagonmath.org/pdf/2611.00485v1) · [Nurowski](https://arxiv.org/abs/2610.04136)

### Bibliography, entry by entry

The file has 32 database entries. The 30 cited entries appear below in PDF order. The two additional entries are unused. I checked names, title, year, and journal pagination or preprint identifier. Modern publisher “published online” dates can precede the issue year in the bibliography. Article numbers 46, 56 and 102277 are identifiers. The PDF original and rebuild agree on all 30 entries. [Primary-source metadata log](../data/n7/allN/hier/r35/primary.log)

| PDF | Entry and check |
| ---: | --- |
| 1 | Albouy and Kaloshin, *Finiteness of central configurations of five bodies in the plane*, Annals 176(1), 535–588 (2012). [Journal](https://annals.math.princeton.edu/2012/176-1/p10) |
| 2 | Chang and Chen, *Toward finiteness … (I) Determine diagrams and orders*, JSC 123, 102277 (2024). [Publisher](https://doi.org/10.1016/j.jsc.2023.102277) |
| 3 | Chang and Chen, Part II, *Determine mass relations*, SIADS 24(3), 2369–2404 (2025). [SIAM](https://doi.org/10.1137/24M1716070) |
| 4 | Zhe Chen and Zhicheng Tong, five-body all-positive preprint, 2026, arXiv:2610.16107. [Record](https://arxiv.org/abs/2610.16107) |
| 5 | Same authors, six-body Part I, 2026, arXiv:2610.23329. The note about the inner v1 title is borne out by the PDF. [Record](https://arxiv.org/abs/2610.23329) |
| 6 | Leonardo de Moura and Sebastian Ullrich, *The Lean 4 theorem prover and programming language*, CADE 28, LNCS 12699, 625–635 (2021). [Springer](https://doi.org/10.1007/978-3-030-79876-5_37) |
| 7 | Thiago Dias and Bo-Yu Pan, cross-symmetric six-body/six-vortex paper, JDDE 32, 1579–1602 (2020). [Publisher](https://doi.org/10.1007/s10884-019-09765-y) |
| 8 | Alexander Grothendieck, EGA IV, third part, IHÉS 28, 5–255 (1966). The new page range matches the edition. [Numdam](https://www.numdam.org/item/PMIHES_1966__28__5_0/) |
| 9 | Marshall Hampton and Richard Moeckel, *Finiteness of relative equilibria of the four-body problem*, Inventiones 163(2), 289–312 (2006). [Publisher](https://doi.org/10.1007/s00222-005-0461-0) |
| 10 | Joos Heintz, quantifier-elimination paper, TCS 24(3), 239–277 (1983). Add the 1985 corrigendum as in B1. [Publisher](https://doi.org/10.1016/0304-3975(83)90002-6) |
| 11 | Q. Huangfu and J. A. J. Hall, *Parallelizing the dual revised simplex method*, Math. Program. Comput. 10, 119–142 (2018). [Publisher](https://doi.org/10.1007/s12532-017-0130-5) |
| 12 | Anders Jensen and Anton Leykin, *Smale’s 6th problem for generic masses*, J. Exp. Math. 1(2), 306–314 (2025). [Journal](https://doi.org/10.56994/JXM.001.002.006) |
| 13 | Kefeng Liu and Yangshanshan Liu, positive five-body preprint, 2026, arXiv:2610.28168. [Record](https://arxiv.org/abs/2610.28168) |
| 14 | Małgorzata Moczurad and Piotr Zgliczyński, planar equal masses, CMDA 131(10), article 46 (2019). [Publisher](https://doi.org/10.1007/s10569-019-9920-6) |
| 15 | Same authors, spatial equal masses, CMDA 132(11–12), article 56 (2020). The planar result is also stated there. [Publisher](https://doi.org/10.1007/s10569-020-09993-1) |
| 16 | Richard Moeckel, *Generic finiteness for Dziobek configurations*, Trans. AMS 353(11), 4673–4686 (2001). [Article](https://doi.org/10.1090/S0002-9947-01-02828-8) |
| 17 | Paweł Nurowski, even-power homogeneous potentials, 2026, arXiv:2610.04136. [Preprint](https://arxiv.org/abs/2610.04136) |
| 18 | Okolo Hanyelichukwu Paul, valuation–lattice preprint, restricted record 23576138 (2026). The public title lacks punctuation between the two clauses; the bibliography supplies a colon. [Deposited metadata](https://zenodo.org/api/records/23576138) |
| 19 | Sam Payne, *Fibers of tropicalization*, Math. Z. 262(2), 301–311 (2009), erratum 272, 1403–1406 (2012). The erratum explicitly preserves Corollary 4.2. [Paper](https://doi.org/10.1007/s00209-008-0374-x) · [Correction](https://web.ma.utexas.edu/users/sampayne/pdf/CorrectionToFibers.pdf) |
| 20 | Bjorn Poonen, *Maximally complete fields*, Enseign. Math. (2) 39, 87–106 (1993). [Author PDF](https://math.mit.edu/~poonen/papers/amsval.pdf) |
| 21 | Gareth E. Roberts, *A continuum of relative equilibria in the five-body problem*, Physica D 127(3–4), 141–145 (1999). [Publisher](https://doi.org/10.1016/S0167-2789(98)00315-7) |
| 22 | Steve Smale, *Mathematical problems for the next century*, Math. Intelligencer 20(2), 7–15 (1998). [Publisher](https://doi.org/10.1007/BF03025291) |
| 23 | The mathlib Community, *The Lean mathematical library*, CPP 2020, 367–381. [Project citation](https://mathlib.org/cite.html) |
| 24 | The Stacks project authors, *The Stacks project*, continuously maintained, cited in 2026. All four numbered tags resolve. [Project](https://stacks.math.columbia.edu) |
| 25 | Pieter Tibboel, relative-equilibria preprint, 2013, arXiv:1305.1728, withdrawn. [Record](https://arxiv.org/abs/1305.1728) |
| 26 | Tejasvi Singh Tomar, special-mass five-body paper, Hexagon 2611.00485v1 (2026). [Paper](https://hexagonmath.org/pdf/2611.00485v1) |
| 27 | Tomar, five bodies in the plane with a Lean proof, arXiv:2610.13100 (2026). The title matches v2. [v2](https://arxiv.org/abs/2610.13100v2) |
| 28 | Tomar, positive generic six-body paper, Zenodo v5 (2026) and a Hexagon copy. Both open and have the cited sections. [Zenodo](https://doi.org/10.5281/zenodo.23720035) · [Hexagon](https://hexagonmath.org/2611.00377v1) |
| 29 | Aurel Wintner, *The Analytical Foundations of Celestial Mechanics*, Princeton Mathematical Series 5, Princeton University Press (1941). [Original edition record](https://books.google.com/books?id=zs0gAAAAMAAJ) |
| 30 | Zhihong Xia, *Central configurations with many small masses*, JDE 91(1), 168–179 (1991), verified on the article. [Publisher](https://doi.org/10.1016/0022-0396(91)90137-X) |
| Unused | Forest Ray Moulton, straight-line solutions, Ann. Math. 12(1), 1–17 (1910), and Thiago Dias, Veronese geometry of Dziobek configurations, arXiv:2601.07962 (2026). These two BibTeX records produce no PDF entries. [Moulton](https://doi.org/10.2307/2007159) · [Dias](https://arxiv.org/abs/2601.07962) |
