# Generic finiteness of planar central configurations for every number of bodies

Paper, formal proofs, computations and the record of the checks.

**Paper:** [`paper/alln/main.pdf`](paper/alln/main.pdf) (source `paper/alln/main.tex`).

## The result

A central configuration of n point masses in the plane is a configuration in which the Newtonian
acceleration of every body points to the centre of mass, with the same factor for all bodies. Smale's
sixth problem asks whether, for every choice of positive masses, there are finitely many of them up to
similarity.

> **Theorem.** For every n ≥ 2 there is a proper Zariski-closed subset Σ_n of C^n, defined over Q, such
> that for positive masses outside Σ_n the planar n-body problem has finitely many central configurations
> up to similarity.

The set Σ_n is not described. The statement was known for n ≤ 5, and two preprints of 2026 prove it for
n = 6 (Tomar; Chen and Tong, Part I). We know no earlier proof for n ≥ 7. The proof has no enumeration of
diagrams and no computation: it bounds, over a field of Hahn series and at masses with widely separated
valuations, the valuation of every squared mutual distance of a solution.

## Status of the claims

Read this before you rely on anything here.

| part | status |
|---|---|
| The statements about valuations: Lemma 3.4 (last sentence), Lemma 4.1, Lemma 5.2, Corollary 5.3, Theorem 6.2 (a), (b), (c) and the inequality of (d), Corollary 6.3 | proved in the paper, and formal counterparts are proved in Lean 4 (`lean/direct-route`); in our runs six proof checkers accepted them |
| The reduction: Lemmas 2.1 to 2.4, Proposition 7.1, Lemma 8.1, and with them Theorems 1.1 to 1.3 | proved in the paper only; not formalised |
| The computations of Section 11 | the searches are evidence, and the exact computation of Remark 9.1 verifies its example; no proof of a theorem, proposition, lemma or corollary uses any of them |

The paper has not been peer reviewed, and no person who works on central configurations or on algebraic
geometry has read the proofs. The mathematics was produced by a language-model agent in sessions that
the author directed, and ten further language-model sessions checked it. Section 13 of the paper says
who did what, and `docs/` holds every report.

## Layout

| path | content |
|---|---|
| `paper/alln/` | the paper: `main.tex`, `references.bib`, `main.pdf` |
| `lean/direct-route/` | the Lean project: three statement files, the proofs, the lists of theorems |
| `scripts/allN/` | the gate for the Lean project, the generators of three proof files, the search and check programs of Section 11 |
| `data/n7/allN/hier/nk/` | the recorded points and the logs of the searches of Table 6 of the paper |
| `data/n7/allN/hier/r29/` to `r35/` | the programs and outputs of the sessions that refereed the work |
| `data/n7/allN/hier/lean/` | the logs of our run of the Lean check on Linux |
| `docs/` | the referee reports, the reviews of the statement files, the prompts, and the texts as the referees read them |

The names `n7`, `allN` and `direct-route` come from the development repository. They are kept so that the
paper, the reports and the programs refer to the same paths.

## Build the paper

    cd paper/alln && latexmk -pdf main.tex

## Check the formal proofs

You need [elan](https://github.com/leanprover/elan); it installs Lean 4.36.0 from `lean-toolchain`. The
Mathlib cache takes about 8 GB of disk.

    cd lean/direct-route
    lake exe cache get        # once
    lake build
    cd ../..
    scripts/allN/lean_gate.sh lean/direct-route/TRUSTED.sha256 --local --final

The last line must begin with `GATE PASS`. The gate first checks that the statement files, the lists of
theorems and the files that select the versions have the digests of `TRUSTED.sha256`, the file that you
pass to it. It then runs `lake comparator` for each of the three lists: every listed theorem must be proved
with the statement of the statement file, with no axiom beyond `propext`, `Quot.sound` and
`Classical.choice`. With `--final` the kernel of Lean and five further checkers judge the proofs; without it
the kernel of Lean alone does.

`--local` runs the comparator without its sandbox, also when `--final` is given: the proof files are then
built with your permissions, so read them or run in a container if you do not trust them. On Linux with
bubblewrap and unprivileged user namespaces you can leave `--local` out. We ran the comparisons on macOS
(ARM) and on Linux (x86-64), both without the sandbox; on our Linux machine the sandbox could not be
started. The logs of the Linux run are in `data/n7/allN/hier/lean/`: the three comparisons with
`--paranoid`, each accepted by the six checkers, and the three failed starts of the sandbox. The host
name is removed from `versions.json` there. The release holds no log of the macOS run. That the six
checkers accepted the proofs is our report of these two runs, and the command above repeats the check.

The digests of the three statement files are printed in the paper (Section 10). Compare them with

    shasum -a 256 lean/direct-route/Challenge.lean lean/direct-route/ChallengeA.lean lean/direct-route/ChallengeB.lean

`lean/direct-route/README.md` maps each statement of the paper to its Lean name.

## Rerun the computations

The check of the recorded points needs only Python 3:

    python3 scripts/allN/nk_cut_check.py data/n7/allN/hier/nk/*/*P.json.gz data/n7/allN/hier/nk/*/BL.json.gz

It reports 2,323 points with no failure of an ultrametric condition or of a cut condition. The check of the
cycle relation and the searches need `numpy` and `highspy`. The check of the cycle relation works within
the tolerance 0.001: it takes the edges whose Ψ is within 0.001 of the largest, and joins a node to its
parent when their heights differ by at most 0.001 (Section 11 of the paper):

    python3 scripts/allN/nk_cycle_check.py data/n7/allN/hier/nk/*/*P.json.gz data/n7/allN/hier/nk/*/BL.json.gz
    python3 scripts/allN/nk_fibre.py 4 0,1,34,1156 --far-psi 3     # a small search, under a minute; the usage is in the file

The files of `data/n7/allN/hier/nk/` and the rows of Table 6 of the paper. Each run has three files: the
points `X.json.gz`, the parts `X.jsonl.gz` and the log `X.log.gz`, whose first line is the command.

| run | n | mass weights | search |
|---|---|---|---|
| `nk5psi_*/HP` | 5 | (0, 1, 12, 150, 1900) | Ψ* ≥ 5; one pair of trees from each class under the exchange of the colours (446,985 pairs, which cover the 893,025 ordered pairs) |
| `nk5psi_*/GP` | 5 | (0, 1, 2.37, 4.91, 8.53) | Ψ* ≥ 3; the same pairs |
| `nk5psi_*/WP` | 5 | (0, 1, 52, 2700, 140000) | Ψ* ≥ 5; the same pairs |
| `nk6s_*/BL` | 6 | (0, 1, 45, 2000, 89000, 3920000) | no threshold; 100,000 ordered pairs of trees, seed 29 |
| `nk6s_*/BP` | 6 | (0, 1, 45, 2000, 89000, 3920000) | Ψ* ≥ 5; 500,000 ordered pairs of trees, seed 29 |
| `nk6s_*/AP` | 6 | (0, 1, 12, 150, 1900, 24000) | Ψ* ≥ 5; 300,000 ordered pairs of trees, seed 29 |

The six-body runs used `scripts/allN/nk_fibre.py` as it is here, with `--abs-tol 0.001`. The five-body runs
used an earlier version, with the option `--sym` and the relative tolerance 1e-7 that is still the default.
That version is `nk_fibre.as-run.py` in their directory; it is a record and is not meant to be run from
there. `versions.json` in each directory holds the SHA-256 digest of the program that the run used. The
field `ray` of a recorded point, and the counts "by ray verdict" in the logs, are the outcome of a search
in floating point, with chosen objectives, for a direction along which the point can move without bound in
its cell: 0 if the search found none, 1 if every direction that it found leaves the set of weight data,
2 if one stays in it. No value is a certificate, and neither the paper nor Table 6 uses this field.

The exact computations are single files and run in a few seconds:

    clang++ -std=c++17 -O2 -o search data/n7/allN/hier/r32/search_alternating.cpp && ./search
    clang++ -std=c++20 -O2 -o check data/n7/allN/hier/r33/check_rank_cycles.cpp && ./check
    clang++ -std=c++20 -O2 -o cycles data/n7/allN/hier/r34/independent_cycles.cpp && ./cycles
    python3 scripts/allN/wd_u0123_check.py

The seven lines that each of the first two prints are lines 2 to 8 of the `.txt` file next to it, which
also has a first line with the compiler command and a last line with the time. The third prints the first
eleven lines of `independent_cycles.log`. The third also gives the 96 cycles of six bodies of Section 11
(its last line). The fourth checks the family of weight data of Remark 9.1.

## The record of the checks

`docs/README.md` lists the ten reports, the prompts that the sessions were given, and the texts as they
were read. These reads are not peer review.

## Licence and citation

The code is under the MIT licence (`LICENSE`): the Lean files, the programs of `scripts/` and the programs
kept under `data/`. The paper, the documents and reports of `docs/`, and the recorded points, logs and
outputs of `data/` are under CC BY 4.0 (`LICENSE-CC-BY-4.0`). To cite this work, see `CITATION.cff`.

## Contact

Keston Aquino-Michaels, No Way Labs: kestonamichaels at gmail.com. Reports of errors are welcome.
