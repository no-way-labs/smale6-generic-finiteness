# Prompt for a cold read of the release

*2026-11-18. For a session with a cleared context, started in the release directory. The text below the
line is the prompt.*

---

You are asked to referee a mathematics paper and the repository that is released with it, as a reader who
has never seen either. The repository is about to be made public. Its main theorem is new for seven or
more bodies if the proof is right. Read as a referee who expects to find an error, and as a stranger who
follows the README and expects it to fail.

**Where you work.** The release is the directory
`[the release directory]`. Read only files inside it, and public
sources on the web. Do not open any other directory of this machine; in particular not
`[the development repository]`. Do not run `git commit`, `git push`, `git checkout` or any command that changes the
repository, and edit no file in it.

**Where you write.** Your report goes to `../R34-report.md`, one level
above the repository, and your programs and outputs to `../r34/`. Create
the report file at once with a one-line header. Build products of your tests (LaTeX, compiled programs)
go to a copy of the tree under `r34/`, not into the repository.

**Rules.** Rent nothing. Keep each local run under 15 minutes and 4 GB, one job at a time. Do not download
the Mathlib cache (8 GB) and do not run `lake build`. Use your own code for every check of the
mathematics, exact arithmetic where a check is meant to prove something, and a control for every search
that finds nothing. At the top of the report state which model you are and which files you opened.

## Part 1. The paper, in full

Read `paper/alln/main.tex` (`main.pdf` is the same text) from the first line to the last, and judge every
proof as it is printed. Form your verdict on Sections 2 to 8 before you open anything in `docs/`.

- Sections 2 to 8: every lemma, proposition and theorem. Earlier readers judged earlier drafts; do not
  rely on that. The places they named as the most delicate: Lemma 5.2, Steps 2 to 4; Theorem 6.2, Steps 1
  and 4; Lemma 8.1 with Remark 8.2; Proposition 7.1.
- **Remark 1.4, the bound.** This claim is new and nobody has checked it: when the number of solutions
  modulo the rotation is finite, it is at most 4^(2n + C(n,2)), by Bézout's inequality applied to the
  solutions with X_01 = 1. Is the count of the equations and their degrees right? Does one point of each
  orbit lie on the slice, and only one? Does the inequality bound the number of points of a finite
  algebraic set cut out by these equations? Is the citation (Heintz 1983) the right source, and which
  theorem of it?
- The statements alone, read in order: can each be read alone, and do they give the argument?
- The abstract, the introduction, Remark 1.4 and the last section: is anything claimed that the paper does
  not prove or the repository does not show?
- Sections 9 to 13 against the repository: Table 4 and the list of differences against the three
  statement files `lean/direct-route/Challenge.lean`, `ChallengeA.lean`, `ChallengeB.lean`; the digests of
  Table 5 against `shasum -a 256` of those files; Section 11 against the data and the programs that it
  names; Section 13 against `docs/`.

## Part 2. The repository, as a stranger

Follow `README.md` from the top.

- Does every command that you are allowed to run work as written? Run: the build of the paper (in a
  copy), the check of the recorded points, the two exact searches, and the comparison of the digests.
  For the Lean check, do not build; read `scripts/allN/lean_gate.sh` and say whether it does what the
  README and Section 10 of the paper say, and whether a reader could be misled about what it proves.
- Does every path that the paper, the READMEs and `docs/README.md` name exist? Does any file refer to
  something that is not in the release in a way that would stop a reader? (The reports and the texts of
  `docs/as-read/` are historical and name files of a development repository; `docs/README.md` says so.
  Judge whether that note is enough.)
- Is the status of each claim (proved in the paper, formalised, evidence) stated the same way in the
  README, in the abstract and in Section 10?
- Do the proof files contain a `sorry`? (`grep` the files of `lean/direct-route/DirectRoute` and
  `Solution*.lean`.) Do the statement files state what Table 4 says?
- Anything that should not be public or that would embarrass the author: a private address, a path of a
  personal machine, an internal note, a broken table, a typo in a theorem, a reference that does not
  resolve in the PDF, an inconsistent number between the paper and a file.

## Part 3. The literature (only with a search tool)

- The three citations that the author could not verify: the theorem of Heintz (1983) used in Remark 1.4;
  Xia's theorem (1991) as the row of Table 1 describes it, against the full text if you can reach it; the
  page range of EGA IV, part 3, in the bibliography.
- Table 1, row by row, against the sources.
- One more search for a proof or a claim of generic finiteness of planar central configurations for some
  n ≥ 7 that Table 1 misses, and for a family of central configurations that contradicts Theorem 1.2 or
  Theorem 1.3.

## The sheet

For each item answer one of: **holds** / **holds with a fix** (give the fix) / **fails** (quote the first
sentence or command that fails and say why) / **not checked**.

| item | what to confirm |
|---|---|
| G1 | Sections 2 and 3: Lemmas 2.1 to 2.4, Lemma 3.2, Definition 3.3, Lemma 3.4, Example 3.5 |
| G2 | Lemma 4.1 and Lemma 5.2, every step; Corollary 5.3; Example 5.4 |
| G3 | Theorem 6.2, Steps 1 to 5; Corollary 6.3; Example 6.4 |
| G4 | Proposition 7.1 and the proof of Theorem 1.3 |
| G5 | Lemma 8.1, the proofs of Theorems 1.2 and 1.1, Remark 8.2 |
| G6 | Remark 1.4: the bound from Bézout's inequality, and its citation |
| G7 | Abstract, introduction and last section claim no more than is proved and shown |
| G8 | Section 10 and Tables 4 and 5 agree with the three statement files; no `sorry` in a proof file |
| G9 | Sections 9 and 11 agree with the programs and the data |
| G10 | Every README command that you ran works as written; every named path exists |
| G11 | Nothing private, broken or inconsistent in the release |
| G12 | The three citations; Table 1; no earlier proof for n ≥ 7 and no counterexample found |

Then, in free text: your verdict on the paper (**sound** / **sound with fixes** / **not sound** / **cannot
say**); your verdict on the release (**ready** / **ready after these changes** / **not ready**); and the
list of changes, most important first.
