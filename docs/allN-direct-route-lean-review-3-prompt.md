# Prompt for the review of the third Lean statement file

*2026-11-17. For a session with a cleared context. The text below the line is the prompt.*

---

You are asked to review a file of formal statements before it is frozen. The file is
`lean/direct-route/ChallengeB.lean` (103 lines, Lean 4 with Mathlib). It states, with `sorry` in place of
each proof, eight theorems that are meant to say what a paper says. Proofs exist in other files and a
checker accepts them. That is not your concern: a checker confirms that the proofs prove the formal
statements, and nobody has yet confirmed that the formal statements say what the paper says. A wrong
statement with a correct proof is the failure you are looking for.

**What to read.**

- `lean/direct-route/ChallengeB.lean`: the file under review.
- `lean/direct-route/Challenge.lean`: the definitions that it uses (`Chamber`, `IsUltra`, `node`,
  `IsCycle`, `psiPair`, `topPairs`, `Datum` and its fields, `cycN`, `inc`, `cycQ`, the examples `ex2`,
  `ex4u`, `ex4z`, `ex4w`). This file was reviewed and frozen before; do not review it again, but read
  each definition that `ChallengeB.lean` uses.
- `paper/alln/main.tex`, Sections 3 to 6 (`paper/alln/main.pdf` is the same text): the statements that
  the file is meant to match. Lemma 4.1, Definition 5.1, Lemma 5.2, Corollary 5.3, Example 5.4,
  Definition 6.1, Theorem 6.2, Example 6.4.

**What you must not open.** The proofs (`lean/direct-route/DirectRoute/`, `Solution*.lean`), the earlier
reviews and referee reports, and the other documents of the repository.

**You may run** `lake env lean ChallengeB.lean` in `lean/direct-route` to see that the file compiles (it
reports a `sorry` warning for each theorem). Do not start a full build; one may be running.

**The questions, for each of the nine declarations** (`IsAltSeq`, `lemmaB_sign`, `lemmaC_alt`,
`cycle_alt_bodies`, `alt_relation`, `cycle_alt`, `psi_star_bound`, `ex2_alt`, `ex4_alt`):

1. Which sentence of the paper does it state? Quote it.
2. Is any hypothesis stronger than in the paper, or any conclusion weaker? Is anything missing?
3. Could it hold for an empty reason (hypotheses that nothing satisfies, a conclusion that is trivially
   true, an index convention that makes a condition vacuous)?

**Places where an error would be easy.**

- `IsAltSeq`: the paper's closed alternating sequence has 2r distinct edges; the structure asks for
  `f` injective, `g` injective and `f i ≠ g j`. Is that the same? The index after r − 1 is written
  `(i + 1) % r`. The heights are functions of an ordered pair `e = (x, y)`; is the direction of the
  two equalities (`HW` between `f i` and `g i`, `HZ` between `g i` and `f (i + 1)`) that of
  Definition 5.1?
- `lemmaB_sign`: "q·u has the sign of q_m" is written as `0 < q_m * (q·u)`. The sums run over the
  indices up to m, as in `lemmaB` of `Challenge.lean`. Is this the statement of Lemma 4.1 when m is the
  largest index with a nonzero coefficient?
- `lemmaC_alt`: the heights are the real numbers `z e.1 e.2` and `w e.1 e.2`. `topPairs` is E°. The
  hypothesis `hn : 2 ≤ n` is present and may be unused.
- `alt_relation`: the heights are `D.dz e.1 e.2` and `D.dw e.1 e.2`, with values in `WithTop ℝ`. For an
  edge of `D.Estar P` both are real, by the definition of `IsEdge`. The first conclusion says that some
  edge of the sequence is an O-edge (`(f i).2 = D.n` or `(g i).2 = D.n`). Signs: `cycN` and `cycQ` give
  −1 to `f` and +1 to `g`; is that Definition 6.1?
- `psi_star_bound`: is the bound that of Theorem 6.2 (d), and is the part of (d) about the finite set
  absent (the paper's table will say so)?
- `cycle_alt_bodies` and `cycle_alt`: these say that the old hypothesis (`IsCycle`, with nodes) implies
  the new one, so that the new statements are at least as strong as the frozen ones. Is that what they
  say?
- `ex2_alt` and `ex4_alt`: do they show that the hypotheses of `alt_relation` can hold, and that
  `lemmaC_alt` is not empty of content outside the chamber?

**Your report.** Write it to `docs/allN-direct-route-lean-review-3.md`. Start with one of: **freeze as
is** / **freeze after these changes** (list them) / **do not freeze** (say why). Then a table with one
row for each declaration: the passage of the paper, and your finding. State which model you are and
which files you opened. Edit no other file and commit nothing.
