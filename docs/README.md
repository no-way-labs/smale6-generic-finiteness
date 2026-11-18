# The record of the checks

Ten language-model sessions checked this work. Each was started with no access to the sessions that
produced it. None of this is peer review. Section 13 of the paper describes the sessions; this directory
holds what they were given and what they wrote. The verdicts and the text of the reports are unchanged.
The changes made for this release concern links, the rendering of one table and directory names:

- the links of R34 and R35 to their own files point to `data/n7/allN/hier/r34/` and `r35/` (each report
  says so in its second line);
- the link in the third line of `n7-referee-R31.md` points to `as-read/R31-write-up.md`, and in two rows
  of its table `|x|` is written `\lvert x\rvert`, so that the table renders;
- the eleven line links of `allN-direct-route-lean-review-3.md` point to `as-read/R33-paper.tex`, the
  text whose line numbers they give;
- in the two prompts for the reads of the release, the directories of the author's machine are written
  as `[the release directory]`, `[the development repository]` and paths relative to the release.

## Reports

| file | what was read | by |
|---|---|---|
| `n7-referee-R29.md` | the working note, `as-read/R29-working-note.md` | Qwen4 Max |
| `n7-referee-R30.md` | the write-up, `as-read/R30-write-up.md` | GPT-6.2 Sol |
| `n7-referee-R31.md` | the write-up, `as-read/R31-write-up.md`, with a search of the literature | GPT-6.2 Sol |
| `n7-referee-R32.md` | a draft of the paper, `as-read/R32-paper.tex` | GPT-6.2 Sol |
| `n7-referee-R33.md` | the changes after R32, in the draft `as-read/R33-paper.tex` | GPT-6.2 Sol |
| `n7-referee-R34.md` | the whole release as a stranger: the paper `as-read/R34-paper.tex`, the repository by its instructions, the literature | GPT-6.2 Sol |
| `n7-referee-R35.md` | the whole release before it was made public: the paper `as-read/R35-paper.tex`, every file, the literature | GPT-6.2 Astra |
| `allN-direct-route-lean-review-1.md` | the statement file `Challenge.lean` | GPT-6.2 Sol |
| `allN-direct-route-lean-review-2.md` | the statement file `ChallengeA.lean` | GPT-6.2 Sol |
| `allN-direct-route-lean-review-3.md` | the statement file `ChallengeB.lean` | GPT-6.2 Sol |

The model names are those of the author's configuration. R32, R33, R34, R35 and the third review name
GPT-6 and no variant; R29, R30, R31 and the first two reviews name no model.

The programs and outputs of the referees are in `data/n7/allN/hier/r29/` to `r35/`.

## Prompts

`allN-paper-referee-prompt.md` (R32), `allN-paper-referee-prompt-2.md` (R33),
`allN-release-read-prompt.md` (R34), `allN-release-read-prompt-2.md` (R35) and
`allN-direct-route-lean-review-3-prompt.md` (the third review) are the prompts as given, with the change
of directory names stated above. The write-up read
by R30 and R31 contains its own instructions to the reader (its sections 0, 10 and 11).

## How to read these files

- The texts of `as-read/` are the versions that the referees judged. R29, R31, R32 and R33 state a commit
  of the development repository, and the file here is the text at that commit; R30 names its write-up, and
  R34 and R35 read the release that was built from the text kept here. They are earlier than the paper and
  differ from it: the paper proves Lemma 5.2 by a shorter argument, states Lemma 8.1 in another form, and
  numbers its statements differently. Where they differ, the paper is the claim and these are the history.
- The reports and the older texts name files of the development repository that are not part of this
  release (for example `docs/allN-status.md` or `docs/allN-hierarchical-emptiness.md`), and commits of
  that repository. Those references do not resolve here. Two of them have a counterpart in the release:
  `docs/allN-direct-route.md` is the working note, of which `as-read/R29-working-note.md` is the version
  that R29 read, and `docs/allN-direct-route-second-read.md` is the write-up, of which
  `as-read/R30-write-up.md` and `as-read/R31-write-up.md` are two versions.
- Comments in the source files name the same development files: the headers of `Challenge.lean` and
  `ChallengeA.lean` ("the brief" is the write-up; "the task" is a work plan that is not released) and the
  docstrings of the programs of `scripts/allN/`. The statement files are fixed by their digests, so these
  comments were left as they are. For what a statement or a program does, the paper is the reference:
  Sections 3 to 6 and 10 for the Lean files, Section 11 for the programs.
- R34 read the release before the corrections that it asked for. `as-read/R34-paper.tex` is the paper as
  it read it; the READMEs, which it also read, have changed since in the places that its report names.
  Its item on the theorem of Heintz quotes the statement of 1983 for constructible sets. The corrigendum
  of 1985 restricts that statement, and Remark 1.4 of the paper uses it for closed sets only.
- R35 read the release before the corrections that it asked for; `as-read/R35-paper.tex` is the paper as
  it read it. Its lists A and B give the lines of that release. `data/n7/allN/hier/r35/list-A.patch` and
  `list-B.patch` are the edits that it proposed; the edits made differ from them in wording. One line of a
  program of R30 was changed at its request: `cert6b.py` printed a total with a fixed number of earlier
  certificates and now prints the number that it counted.
- The first review led to three clearer comments and two further examples in `Challenge.lean`; no review
  asked for a change to the statement of a theorem. The statement files in `lean/direct-route` are the
  final ones.
- The pickled intermediate files of R30 (`*.pkl`) are left out; its programs write them again. Run them
  inside `data/n7/allN/hier/r30/` in this order: `check2.py N` for N = 3, 4, 5 and `check6fast.py` (the
  enumerations), then `lp6.py`, `cert6.py`, `cert6b.py` (the linear programs and certificates at six
  bodies, which read the output of `check6fast.py`); `d4n4.py`, `d4n4b.py`, `run6.py` and `n7rand.py`
  stand alone. They need `numpy` and `scipy`. We did not rerun them for this release;
  `data/n7/allN/hier/r34/independent_cycles.cpp` repeats the enumeration.
