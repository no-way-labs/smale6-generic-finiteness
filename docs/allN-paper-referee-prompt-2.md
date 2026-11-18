# Prompt for a second read of the paper draft: the fixes after R32

*2026-11-17. For a session with a cleared context. The text below the line is the prompt.*

---

You are asked to check the changes that were made to a mathematics paper after a referee's report. The
referee (report R32) read the paper at commit `66ca227`, judged it sound with fixes, and asked for one
repair of a proof and for a list of corrections. The authors applied them. Nobody independent has read
the new text. Your task is to read it as a referee who expects that a fix introduced an error.

**What to read.**

- The paper now: `paper/alln/main.tex` (`paper/alln/main.pdf` is the same text) and
  `paper/alln/references.bib`.
- The changes: `git diff 66ca227 HEAD -- paper/alln/main.tex paper/alln/references.bib`.
- The report that the changes answer: `docs/n7-referee-R32.md`.
- For item F8 only: `lean/direct-route/Challenge.lean` and `lean/direct-route/ChallengeA.lean`.
- For item F9 only: `data/n7/allN/hier/r32/search_alternating.cpp` and its output
  `search_alternating.txt` in the same directory.
- Public sources on the web, if you have a search tool.

**What you must not open.** Any other file of the repository, in particular `docs/allN-direct-route*.md`,
the other referee reports, `docs/n7-referee-log.md`, `docs/allN-status.md`, and the Lean proofs in
`lean/direct-route/DirectRoute/`.

**Rules.** Edit no file except your own report and scripts. Commit nothing. Rent nothing. Keep each local
run under 15 minutes and 4 GB. Use your own code for every check, and exact arithmetic where a check is
meant to prove something.

**Your report.** Take the lowest number NN ≥ 33 for which `docs/n7-referee-RNN.md` does not exist and
create that file at once with a one-line header. Scripts and outputs go to `data/n7/allN/hier/rNN/`. At the
top state which model you are, the commit of the paper that you read
(`git log -1 --format=%h -- paper/alln/main.tex`), and which files you opened. End with the sheet below.

## The changes to check

For each item: is the new text correct, does it do what R32 asked, and did it break anything near it?

- **F1. Lemma 3.2 (d) and the sentence after Definition 3.1.** The proof of (d) now uses two ultrametric
  inequalities at the fixed threshold h. The sentence after Definition 3.1 says that with d_xx = +∞ the
  inequality d_xz ≥ min(d_xy, d_yz) holds for all x, y, z, distinct or not. Check that claim, then read
  the whole proof of Lemma 3.2 again with it: does every use of the inequality hold when two of the three
  indices agree, and when a value is +∞? Then check the three places that use Lemma 3.2: the paragraph
  after Definition 5.1, and Steps 1 and 3 of Theorem 6.2.
- **F2. Proposition 7.1.** The statement now names the system and the masses. Step 3 gives the inverse of
  the map K* × V_1 → V. Is that inverse a morphism into K* × V_1, and does the dimension statement follow?
  Step 4 now cites Tomar's §2.1 for a similar quadratic; check the citation if you can.
- **F3. The paragraph before Lemma 8.1 and the proof of Lemma 8.1.** New: the definition of the fibre
  dimension at a point; the sentences on closed points, density and the correspondence of irreducible
  components over an algebraically closed field; in the proof, "affine and of finite presentation" and
  "a closed subset of a Noetherian scheme" for tag 054K; parts (1) and (3) of tag 02FY; the chain of
  equivalences at the end of (a). Is each sentence true as stated, and is the chain complete?
- **F4. Remark 8.2.** The argument with Payne's Corollary 4.2 is written out: an open subset U of the
  closure Σ of D that lies in D and is dense in every component; the extension to K; the part in the
  torus; each irreducible component lies over a component of Σ and meets the extension of U; density of a
  valuation fibre on that component; the contradiction with Lemma 8.1 (a) and Theorem 1.3. Check every
  step. In particular: does such a U exist; is "meets the extension of U" justified; does Payne's
  corollary (with Remark 2 of the erratum) apply to an irreducible closed subvariety of a torus over K
  and to a valuation vector with real, possibly irrational, coordinates; what happens to a component of
  Σ that lies in a coordinate hyperplane?
- **F5. Section 5.** The description of the multigraph Γ(E) with its two sets of vertices, the case
  r = 1, and the set E° in the statement of Lemma 5.2. Is Definition 5.1 with this paragraph enough to
  read Corollary 5.3 and Theorem 6.2 (a)?
- **F6. Claims.** The abstract, the first paragraphs of the introduction, Remark 1.4, the Method
  paragraph and the paragraph "Formal proof and computations". Check: the definition of a similarity
  and the sentence that finiteness with reflections is the same as without; the three-body count;
  "continuum of solutions modulo rotation" and "close approach" wherever they occur; that the two
  summaries of the Lean coverage agree with Table 4; that the sentence "we attempt no count" is the only
  statement about the number of configurations. Is anything claimed that Sections 2 to 8 do not prove?
- **F7. Literature** (only with a search tool; otherwise "not checked"). The two new rows of Table 1 and
  the sentence about seven bodies (Moczurad and Zgliczyński 2019 and 2020: what exactly is proved, for
  which n, and is "computer-assisted" right?); the changed rows of Chen and Tong, Dias and Pan, Moeckel
  and Xia; in the Method paragraph and after Lemma 3.4, the locations in Albouy and Kaloshin (§2 system
  (4); Lemma 1; the proofs of Theorems 3 and 6; Rule 1c on p. 546) and in Tomar's version 5 (§2.1, §2.3,
  §4.1, §9.1); the description of Jensen and Leykin's method.
- **F8. Section 10.** Table 4 as it now stands, the list of differences (items 2 and 8 are new or
  changed), the sentence on the placeholder `sorry`, and "for all n and all τ ≥ 0". Compare with the two
  statement files.
- **F9. Section 11 and Section 13.** The new paragraph on the exact search: does it describe what
  `search_alternating.cpp` does and what its output shows (the vector, the counts 9,012 and 40,612,578,
  the count 82 of the control)? Is "evidence" the right status for it? In Section 13: is the account of
  the sixth session consistent with R32's report?
- **F10. Anything else in the diff** that F1 to F9 do not name. List each such change and say whether it
  is correct.

## The sheet

For each item answer one of: **holds** / **holds with a fix** (give the fix) / **fails** (quote the first
sentence that fails and say why) / **not checked**.

| item | what to confirm |
|---|---|
| F1 | Lemma 3.2 with the new sentence and the new proof of (d); its three uses |
| F2 | Proposition 7.1: statement, Step 3, the citation in Step 4 |
| F3 | The paragraph before Lemma 8.1 and the proof of Lemma 8.1 |
| F4 | Remark 8.2, every step of the argument with Payne's corollary |
| F5 | Section 5: Γ(E), r = 1, the statement of Lemma 5.2 |
| F6 | Abstract, introduction, Remark 1.4, Method, the summaries of the Lean coverage |
| F7 | Table 1 and the citation locations |
| F8 | Table 4, the differences, the sentence on `sorry` |
| F9 | The paragraph on the exact search; Section 13 on the sixth session |
| F10 | Every other change in the diff |

Then, in free text: your verdict on the changes (**correct** / **correct with fixes** / **an error was
introduced**), and any request of R32 that was not carried out and should have been.
