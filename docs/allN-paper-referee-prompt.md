# Prompt for a referee of the paper draft

*2026-11-17. For a session with a cleared context. The text below the line is the prompt. It names the
paper by its file; the referee states the commit it read.*

---

You are asked to referee a mathematics paper. Its main theorem is new for seven or more bodies if the
proof is right, and we do not trust the proof yet. Read it as a referee who expects to find an error.

**The paper.** `paper/alln/main.tex` in this repository (`paper/alln/main.pdf` is the same text, 19
pages). Title: "Generic finiteness of planar central configurations for every number of bodies". It
claims that for every n ≥ 2 the planar n-body problem has finitely many central configurations up to
similarity for positive masses outside a proper Zariski-closed subset of C^n.

**What you may open.** The paper, its bibliography `paper/alln/references.bib`, and, for part D below
only, the two Lean statement files `lean/direct-route/Challenge.lean` and
`lean/direct-route/ChallengeA.lean`. Public sources on the web, if you have a search tool.

**What you must not open.** Any other file of the repository. In particular: `docs/allN-direct-route*.md`,
the earlier referee reports `docs/n7-referee-R*.md`, `docs/n7-referee-log.md`, `docs/allN-status.md`, the
Lean proofs in `lean/direct-route/DirectRoute/`, and the scripts and data that the paper names. Other
referees may be at work at the same time; do not read their reports. Judge the proofs as they are printed
in the paper. A formal proof exists for some statements (Section 10 of the paper); it is no evidence that
the printed argument is complete, and the printed argument is what you are asked to judge.

**Rules.** Edit no file except your own report and scripts. Commit nothing. Rent nothing. Keep each local
run under 15 minutes and 4 GB, and run one job at a time. Use your own code for every check. Use exact
arithmetic (integers, rationals) where a check is meant to prove something, and say which checks are
floating point. A search that finds nothing must come with a control: the same search on an input where
the object is known to exist.

**Your report.** Take the lowest number NN ≥ 32 for which `docs/n7-referee-RNN.md` does not exist and
create that file at once with a one-line header, so that no other referee takes the number. Scripts and
outputs go to `data/n7/allN/hier/rNN/`. At the top of the report state: which model you are, the commit of
the paper that you read (`git log -1 --format=%h -- paper/alln/main.tex`), and which files you opened.
End the report with the sheet below, filled in.

## Part A. The three proofs that no referee has read (the main task)

These are printed in a new form. Read every line and try to break each step.

1. **Lemma 5.2 (no closed alternating sequence in E°), with Lemma 4.1.** Places where we would look
   first:
   - Lemma 4.1: the statement on the sign of q·u, and the case p = 1.
   - Step 1: the bound |q_j| ≤ n − 1 and the count of the terms in the sum of Lemma 4.1.
   - Step 2: the identity (5.2), also for i = r; the three properties of the integers a_k(i) − b_k(j), in
     particular the bound by n.
   - Step 3: the existence of the two positions i and j with (5.3). Is the cyclic sequence what the text
     says, and can the least value be entered and left only as stated?
   - Step 4: the identification of the four heights (also when j = r − 1), the reduction to four cases,
     the two cases that end in u_L ≤ u_x′ and u_L ≤ u_x, and the two that use Lemma 4.1 (the sum of the
     coefficients of ν, ν_L = −1, the zero coefficients beyond L, the bound |ν_k| ≤ n + 1, the threshold).
   - Does the proof use anything about the sequence beyond what Definition 5.1 gives (2r distinct pairs,
     equal heights)? Is the lemma true as stated for r = 1?
   - Corollary 5.3 and Example 5.4.
   A useful test: an exact search for a counterexample at small n. For n ≤ 5 or 6, enumerate pairs of
   ultrametrics (or pairs of trees with heights from an exact LP or a grid) over a vector u in W_n(n²),
   and look for a closed alternating sequence in E°. Control: the vector (0, 0, 1, 1) of Example 5.4,
   where one exists.
2. **Lemma 8.1 and the proofs of Theorems 1.2 and 1.1 from it, with Lemma 2.4.** This is algebraic
   geometry over Q and over a field of Hahn series. Places where we would look first:
   - Is the scheme of the solutions over a field k the fibre of 𝒳 at the point below m, extended to k?
     Does the non-reduced structure matter anywhere?
   - The set 𝒳_{≥2}: closed by Stacks tag 02FZ. Open the tag and check that it says this for a morphism
     that is locally of finite type.
   - D = π(𝒳_{≥2}) constructible by tag 054K. Check the hypotheses.
   - Part (a): the use of tag 02FY (dimension of a fibre at a point under an extension of the base field;
     every point of the fibre is the image of a point of the extended fibre). Then: "a point at which
     the dimension is at least 2 exists if and only if an irreducible component has dimension at least
     2", and the passage to Lemma 2.4, which is about the closed set of solutions in k, a classical
     variety. Is anything lost between scheme points and solutions in k?
   - Part (b): tag 005K, and the claim that the point below (T^{u*_t}) is the generic point.
   - The proof of Theorem 1.2: from "D is not dense" to a nonzero polynomial H over Q with H(m) = 0 at
     every complex m with infinitely many solutions modulo the rotation. Is Σ_n proper, closed, and
     defined over Q?
   - Lemma 2.4: a connected group maps each irreducible component to itself; an orbit in a component of
     dimension 1 contains a nonempty open subset of it. Is "finitely many orbits if and only if no
     component of dimension at least 2" proved in both directions?
   - Is K algebraically closed, as cited (Poonen, Theorem 1 and Corollary 4)? Check the citation if you
     can.
3. **Proposition 7.1 and the proof of Theorem 1.3.** The claim is that a common upper bound for
   v(X_tl Y_tl) at all solutions over K excludes a component of dimension at least 2. Places where we
   would look first:
   - Step 1: the image of a regular function on an irreducible variety is one point or all of K but
     finitely many elements; elements of every valuation.
   - Step 3: the slice X_ab = 1 and its dimension.
   - Step 4: the quadratic equation, its leading coefficient, and why V_1 is finite. The case n = 2.
   - The proof of Theorem 1.3: does Corollary 6.3 give a bound M that does not depend on the solution?

## Part B. The rest of the argument

4. **Lemmas 2.1 to 2.3:** the passage from central configurations to the system 𝒩_n. Does finiteness of
   the solutions modulo the rotation give finiteness up to similarity? Where is the positivity of the
   masses used?
5. **Section 3:** Lemma 3.2 (the four facts about nodes), Definition 3.3 (in particular the terms of a
   cut and the cut condition when ξ_t or η_t is +∞), Lemma 3.4, Example 3.5.
6. **Theorem 6.2 and Corollary 6.3.** Step 1 is printed with a new choice of the set S (a child of the
   node that contains one end of e and not O); check it with care, also when an end of e is O and when
   Y_p = 0 for a body p of S. Then Step 2 (the signs, N = 3σ, the sum of the q_j), Step 3 (the
   restriction to the bodies), Step 4 (parity, the bound on |q_j|, the threshold), Step 5. Parts (b) and
   (c) are stated for closed alternating sequences, which is more than simple cycles: is that proved?

## Part C. The statements and the claims around them

7. **Read the statements alone, in order** (definitions, lemmas, propositions, theorems, corollaries,
   without the proofs). Can each be read alone? Do they give the argument? Is any hypothesis missing
   from a statement and used in its proof, or stated and never used? Is a symbol used with two meanings?
8. **The abstract, the introduction and Remark 1.4.** Is every claim there supported by a later section,
   and is the scope of the theorems stated without a larger claim anywhere?
9. **The literature** (only if you have a search tool; otherwise answer "not checked"). Check each row
   of Table 1 against its source. Check these citations, which we could not verify: Albouy and Kaloshin,
   "Rule 1c" and the principle used for Proposition 7.1 (give the exact location in their paper);
   Albouy and Kaloshin, p. 543 and Remark 8 for the continuum at the masses (4, 4, 4, 4, 1); Tomar's
   six-body paper, §4.1 and §9, in version 5; the description of Xia's theorem; Payne's Corollary 4.2
   as used in Remark 8.2. Search for a proof or a claim of the theorem for some n ≥ 7 that Table 1
   misses, and for a family of central configurations that contradicts Theorem 1.2 or Theorem 1.3.

## Part D. The formal statements (lower priority)

10. Compare Table 4 and the list "Differences between the formal statements and the text" in Section 10
    with `Challenge.lean` and `ChallengeA.lean`. Does each row say what the formal statement covers? Is a
    difference missing from the list? Do not judge the Lean proofs.

## The sheet

For each item answer one of: **holds** / **holds with a fix** (give the fix) / **fails** (quote the first
sentence that fails and say why) / **not checked**.

| item | what to confirm |
|---|---|
| P1 | Lemma 4.1 and Lemma 5.2, every step; Corollary 5.3; Example 5.4 |
| P2 | Lemma 2.4 |
| P3 | Lemma 8.1 (a) and (b), with the four Stacks tags opened |
| P4 | Theorems 1.2 and 1.1 follow from Theorem 1.3, Lemma 8.1 and Lemmas 2.1, 2.2 |
| P5 | Proposition 7.1, and Theorem 1.3 from it |
| P6 | Lemmas 2.1 to 2.3 |
| P7 | Section 3: Lemma 3.2, Definition 3.3, Lemma 3.4, Example 3.5 |
| P8 | Theorem 6.2 (Steps 1 to 5) and Corollary 6.3 |
| P9 | The statements can be read alone and give the argument; notation is consistent |
| P10 | Abstract, introduction and Remark 1.4 claim no more than is proved |
| P11 | Table 1 and the citations of item 9; no counterexample and no earlier proof for n ≥ 7 found |
| P12 | Table 4 and the list of differences agree with the two statement files |

Then, in free text:

- Your verdict on the paper: **sound** / **sound with fixes** / **not sound** / **cannot say**.
- The steps that you would want a specialist to read before the paper is shown to anyone, in order of
  risk.
- Defects of exposition that would stop a reader (not a list of style points).
