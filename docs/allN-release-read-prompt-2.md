# Prompt for the last read of the release before it is made public

*2026-11-18. For a session with a cleared context, started in the release directory. The text below the
line is the prompt.*

---

You are asked to review a repository from top to bottom on the day it is made public. It holds a
mathematics paper, its formal proofs in Lean, programs, data, and the reports of earlier readers. The main
theorem of the paper is new for seven or more bodies if the proof is right. Once the repository is public,
every error in it is public as well. Read as a referee who expects to find an error in the paper, and as a
stranger who expects the instructions to fail.

**Where you work.** The release is the directory
`[the release directory]`. Read only files inside it, and public
sources on the web. Do not open any other directory of this machine; in particular not
`[the development repository]`. Do not run `git commit`, `git push`, `git checkout`, `git add`, `git reset` or any
command that changes the repository, and edit no file in it. The tree is staged on a local branch with no
commit yet; leave it so.

**Where you write.** Your report goes to `../R35-report.md`, one level
above the repository, and your programs and outputs to `../r35/`. Create
the report file at once with a one-line header. Build products of your tests (LaTeX, compiled programs)
go to a copy of the tree under `r35/`, not into the repository.

**Rules.** Rent nothing. Keep each local run under 15 minutes and 4 GB, one job at a time. Do not download
the Mathlib cache (8 GB) and do not run `lake build`. Use your own code for every check of the
mathematics, exact arithmetic where a check is meant to prove something, and a control for every search
that finds nothing. At the top of the report state which model you are and which files you opened.

**Order of the report.** The author acts on your report today. Put first the list of what must change
before the repository is public, then the rest. For every change give the file, the line, the sentence as
it stands, and the sentence that should replace it, so that it can be applied without a further question.

## Part 1. The paper, from the first line to the last

Read `paper/alln/main.tex` (`main.pdf` is the same text) in full and judge every proof as it is printed.
Form your verdict on Sections 2 to 8 before you open anything in `docs/`.

- Sections 2 to 8: every lemma, proposition and theorem. Earlier readers judged earlier texts; do not rely
  on them. The places they named as the most delicate: Lemma 5.2, Steps 2 to 4; Theorem 6.2, Steps 1 and
  4; Lemma 8.1 with Remark 8.2; Proposition 7.1.
- **What no reader has seen.** The paper changed after the last read. `docs/as-read/R34-paper.tex` is the
  text of that read; compare it with `paper/alln/main.tex` and judge every changed sentence. Three changes
  carry mathematics:
  - **Remark 9.1** is new in this form. It claims that at u = (0, 1, 2, 3), for every real χ > 3, the
    printed heights form a weight datum with Ψ* = χ whose set E* is the closed alternating sequence
    {0,2}, {2,O}, {0,O}, {0,3}, with N = 0 and q = (1, 0, -3, 2), and therefore that Theorem 6.2 (c) and
    (d) fail at this u. Check the claim from Definition 3.3 with your own exact code, for the family and
    not only at one value of χ. Then read `scripts/allN/wd_u0123_check.py`: does its method (polynomials
    of degree at most 1, compared for large χ, with the crossing points recorded) prove what the remark
    says, for every real χ > 3? Is 3 the right bound? Does the remark contradict any statement of the
    paper or of the Lean files? Is the sentence on Lemma 4.1 and W_4(τ) for τ ≥ 1/2 right?
  - **Remark 1.4**: the bound 4^(2n + C(n,2)), now with Heintz (1983), Theorem 1, for closed subsets of an
    affine space, over an algebraically closed field, with exactly one solution of each orbit on the
    slice X_01 = 1. Is every step of this right, and is the cited theorem stated for the sets used?
  - **Section 11**, rewritten: every number and every attribution against the logs and the programs (Part
    2).
- The statements alone, read in order: can each be read alone, and do they give the argument?
- The abstract, the introduction and Sections 9 to 13: is anything claimed that the paper does not prove
  or the repository does not show? Is the status of each claim (proved in the paper, formalised, evidence)
  the same in the abstract, in Section 10 and in `README.md`?
- The PDF as a reader sees it: every page, every table, every reference and citation resolved, the
  bibliography entry by entry (authors, titles, years, pages, links that open).

## Part 2. The repository, file by file

Go through the whole tree; `FILES.sha256` lists every file. For each directory say what you checked.

- **README.md**, from the top. Run every command that you are allowed to run, as written, in a copy: the
  build of the paper, the check of the recorded points, the check of the cycle relation, the small search,
  the four exact computations, the comparison of the digests. For the Lean check, do not build; read
  `scripts/allN/lean_gate.sh`, the three `comparator*.json` and `TRUSTED.sha256`, and the logs in
  `data/n7/allN/hier/lean/`, and say whether the README and Section 10 describe correctly what was run
  and what it shows.
- **Lean.** `grep` the proof files (`lean/direct-route/DirectRoute/*.lean`, `Solution*.lean`) for
  `sorry`, `admit`, `sorryAx`, `axiom`, `unsafe`, `native_decide`, `implemented_by`. Compare the three
  statement files with Table 4, with the list of differences in Section 10 and with
  `lean/direct-route/README.md`, name by name. Compare their digests with Table 5 and with
  `TRUSTED.sha256`.
- **Section 11 against the data.** For each row of Table 6: the command in the first line of the log, the
  number of pairs of trees, the tolerance, the number of points, the largest Ψ*, the bound. The version of
  the program that each run used (`versions.json`) against the files in the release. Each control that
  the section describes against a file that shows it. The counts of the exact computations against their
  outputs.
- **Section 13 and `docs/README.md` against `docs/`.** Is each of the nine sessions described as its
  report describes itself? Does the paper say anything about a report that the report does not support?
  Do the notes of `docs/README.md` on the historical files suffice for a reader who opens one of them?
- **Paths and links.** Every path that the paper, the three READMEs and `CITATION.cff` name: does it
  exist? Every link: does it open? The address of the repository in the paper will resolve only after the
  repository is public; say so and do not count it as an error.
- **What must not be public.** Search every file, the compressed ones after decompression, the PDF by its
  text and its metadata: an e-mail address, a path of a personal machine, a host name, a token or key, a
  name of a private service, an internal note, a remark about a person. Say what you searched for and with
  which control. Two points are decided by the author and are not findings: the header "Keston
  Aquino-Michaels with Claude" of `docs/as-read/R29-working-note.md` stays, and the release has no e-mail
  address of the author, who will add one to the README. Then read as the author's colleague would: anything that would embarrass the author,
  such as a broken table, a typo in a theorem, a number that differs between two files, a claim of novelty
  that the literature contradicts, a sentence that overstates what a language model or a proof checker
  did.
- **Licence and citation.** The author has chosen the MIT licence for the code and CC BY 4.0 for the paper
  and the documents; do not question the choice. Do `LICENSE`, `LICENSE-CC-BY-4.0`, `CITATION.cff` and the
  last section of the README agree with each other and with the content (code, paper, documents, data,
  the reports of the sessions)? Does `CITATION.cff` parse, and are its title, author and address of the repository those of
  the paper?
- **The repository itself.** `git status`, the branch, the remote and `.gitignore`, read only: is anything
  staged that should not be, or left out that the READMEs name? Is any file large enough to be a problem?

## Part 3. The literature (only with a search tool)

- Table 1, row by row, against the sources, and the sentences of the introduction about them.
- Heintz (1983), Theorem 1: the statement, the page, and the sets for which it holds (see the corrigendum
  of 1985).
- **Xia (1991), "Central configurations with many small masses", J. Differential Equations 91, 168 to
  179, against its full text.** No reader has seen more than the publisher's abstract. The row of Table 1
  says: all n; some open sets of positive masses in the usual topology; published; the configurations
  are counted. The introduction says that the result holds on open sets of masses in the usual topology
  and says nothing outside them. Confirm from the theorems of the paper itself: which masses (how many
  are small, and whether the set is open in the space of all n masses), whether the configurations are
  planar, and whether the count is exact. If the file `../xia1991.pdf`
  exists, read it; it is the one file outside the release that you may open. Otherwise try the
  publisher's open archive, the author's page and library mirrors, and say which routes failed.
- A last search, dated today, for a proof or a claim of generic finiteness of planar central
  configurations for some n ≥ 7, and for a family of central configurations that contradicts Theorem 1.2
  or Theorem 1.3.

## The sheet

For each item answer one of: **holds** / **holds with a fix** (give the fix) / **fails** (quote the first
sentence or command that fails and say why) / **not checked**.

| item | what to confirm |
|---|---|
| H1 | Sections 2 and 3, every statement and proof |
| H2 | Sections 4 and 5: Lemma 4.1, Lemma 5.2 step by step, Corollary 5.3, Example 5.4 |
| H3 | Section 6: Theorem 6.2, Steps 1 to 5; Corollary 6.3; Example 6.4 |
| H4 | Sections 7 and 8: Proposition 7.1, Lemma 8.1, the proofs of Theorems 1.1 to 1.3, Remark 8.2 |
| H5 | Remark 9.1: the family of weight data and its program, checked with your own exact code |
| H6 | Remark 1.4 and its citation; Remark 9.2; Table 3 |
| H7 | Every sentence that changed since `docs/as-read/R34-paper.tex` |
| H8 | Abstract, introduction, Sections 12 and 13 claim no more than is proved and shown |
| H9 | Section 10, Tables 4 and 5, the statement files, the gate; no placeholder in a proof file |
| H10 | Section 11 and Table 6 against the logs, the programs and the outputs |
| H11 | Every README command that you ran works as written; every named path exists; every link opens |
| H12 | Nothing private, broken, inconsistent or overstated in any file of the release |
| H13 | Licence, citation file and the state of the repository |
| H14 | Table 1 and the bibliography; Xia (1991) against its full text; no earlier proof for n ≥ 7 and no counterexample found |

Then, in free text and at the top of the report:

1. Your verdict on the paper: **sound** / **sound with fixes** / **not sound** / **cannot say**.
2. Your verdict on making the repository public today: **yes** / **yes after the changes of list A** /
   **no**.
3. **List A**: what must change before it is public, most important first, each with file, line, present
   text and replacement.
4. **List B**: what should change soon after, in the same form.
5. What you did not check.
