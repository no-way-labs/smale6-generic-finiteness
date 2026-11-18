# The formal proofs

Lean 4.36.0 with Mathlib at the tag `v4.36.0`. The statements are those of Sections 3 to 6 of the paper
(`paper/alln/main.tex`). Section 10 of the paper describes what is covered and how the formal statements
differ from the text.

## Files

| file | content | trusted |
|---|---|---|
| `Challenge.lean` (280 lines) | the definitions; the statements for simple cycles; six examples | yes |
| `ChallengeA.lean` (57 lines) | a solution of the system over a valued field; Lemma 3.4; Corollary 6.3 at a solution | yes |
| `ChallengeB.lean` (103 lines) | closed alternating sequences; Lemma 4.1 with the sign; Lemma 5.2; Theorem 6.2 (b), (c) and the inequality of (d) | yes |
| `comparator.json`, `comparatorA.json`, `comparatorB.json` | for each statement file: the names of its theorems and the permitted axioms | yes |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | what is built, and against which Lean and Mathlib | yes |
| `TRUSTED.sha256` | the SHA-256 digests of the nine files above | |
| `Solution.lean`, `SolutionA.lean`, `SolutionB.lean` | the same statements with their proofs | no |
| `DirectRoute/*.lean` | the proofs | no |

In a statement file every theorem has the proof `sorry`. That is how `lake comparator` works: a reader
reads the statements alone, and the comparator checks that the solution file proves the same statements
with no axiom beyond `propext`, `Quot.sound` and `Classical.choice`. The proof files contain no `sorry`.

"Trusted" means: to believe the formal result you read these files and trust Lean, Mathlib and the
comparator. You do not need to read the proofs.

## Check

    lake exe cache get        # once, about 8 GB
    lake build
    ../../scripts/allN/lean_gate.sh TRUSTED.sha256 --local --final      # the last line begins with GATE PASS

See the README at the root of the repository for what the gate does.

## The statements and the paper

| Lean | paper |
|---|---|
| `Chamber` | the chamber W_n(τ), equation (1.5) |
| `IsUltra`, `node` | Definition 3.1 |
| `Datum` and its fields; `Datum.IsEdge`, `Datum.psiE`, `Datum.IsPsiStar`, `Datum.Estar`; `Datum.phiZ`, `Datum.phiW`, `Datum.termsZ`, `Datum.termsW`, `Datum.CutZ`, `Datum.CutW`; `Datum.IsWeightDatum` | Definition 3.3 |
| `IsSolution`, `weights` | the system (1.2) to (1.4) and the weights of a solution, Section 3 |
| `lemmaA` | Lemma 3.4, last sentence |
| `lemmaB`, `lemmaB_sign` | Lemma 4.1 |
| `IsCycle`, `IsAltSeq` | Definition 5.1: simple cycle, closed alternating sequence |
| `psiPair`, `topPairs` | Ψ on the body pairs and the set E°, Section 5 |
| `lemmaC_alt` | Lemma 5.2 |
| `lemmaC`, `cycle_alt_bodies` | Corollary 5.3 |
| `cycN`, `inc`, `cycQ` | Definition 6.1 |
| `degree_two`, `exists_cycle` | Theorem 6.2 (a) |
| `alt_relation`, `cycle_relation`, `cycle_alt` | Theorem 6.2 (b), (c) |
| `psi_star_bound` | Theorem 6.2 (d), the inequality |
| `collision_bound`, `solution_bound` | Corollary 6.3 |
| `chamber_nonempty` | the chamber is not empty, Section 4 |
| `ex2_spec`, `ex2_alt` | Examples 3.5 and 6.4 |
| `ex4_cycle`, `ex4_alt` | Example 5.4 |
| `ex3_spec`, `ex3c_spec`, `ex3m_spec` | three further weight data, not in the paper: one with a body at the origin, one over a vector of the chamber W_3(18), one with different bodies at the origin in the two colours |

Not formalised: Lemmas 2.1 to 2.4, Lemma 3.2 as a statement, the cut identities and the valuations of
their terms in Lemma 3.4, the finite set of Theorem 6.2 (d), Proposition 7.1, Lemma 8.1, and Theorems 1.1
to 1.3.

## The proof files

| file | content |
|---|---|
| `DirectRoute/Defs.lean`, `DefsA.lean`, `DefsB.lean` | the definitions of the statement files, copied; the comparator checks that they agree |
| `DirectRoute/LemmaB.lean` | Lemma 4.1 without the sign |
| `DirectRoute/LemmaC.lean` | Lemma 5.2 for a periodic sequence of pairs with equal heights, and Corollary 5.3 |
| `DirectRoute/Degree.lean` | Theorem 6.2 (a), first sentence; written by `scripts/allN/lean_gen_degree.py` from one template for the two colours |
| `DirectRoute/Cycle.lean` | Theorem 6.2 (a), the simple cycle; Corollary 6.3 |
| `DirectRoute/Relation.lean` | Theorem 6.2 (b), (c) for simple cycles |
| `DirectRoute/Alt.lean` | Lemma 4.1 with the sign, Lemma 5.2, Theorem 6.2 (b), (c) for closed alternating sequences and the inequality of (d); written by `scripts/allN/lean_gen_alt.py` from `Relation.lean` |
| `DirectRoute/LemmaA.lean` | Lemma 3.4 and Corollary 6.3 at a solution; written by `scripts/allN/lean_gen_lemmaA.py` |
| `DirectRoute/Examples.lean` | the examples |
