freeze as is

Brief citations refer to `allN-direct-route-second-read.md`.

| Declaration in `ChallengeA.lean` | Passage in the brief | Finding |
| --- | --- | --- |
| `IsSolution`, lines 23–27 | §1, lines 56–61. “Unknowns `X_t`, `Y_t` for `t = 0, …, n − 1` and `P_tl = P_lt` for `t ≠ l`.” | The symmetry condition matches. Its diagonal case is reflexive. (N1) squares `Pf` and (N2) and (N3) cube it. `(range n).erase t` gives exactly `l ≠ t` among the bodies. Symmetry and the equations are the only constraints. |
| `weights`, lines 32–38 | §2, lines 89–94. “For masses `m_t ∈ K^*` put `u_t = v(m_t)`.” Line 94 gives `ξ_t = v(X_t)`, `η_t = v(Y_t)`, `ζ_tl = v(X_tl)`, and `ω_tl = v(Y_tl)`. | `u` holds the mass valuation. `z` holds `ζ` and `w` holds `ω`. `xi` and `eta` preserve `⊤`. Nonzero masses and (N1) make the entries used as reals finite. The diagonal fallback enters only reflexive symmetry. Each cut guards its origin terms in its own colour. |
| `lemmaA`, lines 42–44 | §2, line 156. “By Lemma A the weights of a solution over K form a weight datum.” | The hypotheses are a solution, nonzero masses, and `n ≥ 2`. Allowing any field with this valuation weakens the Hahn field assumption. The field and valuation laws suffice for the weight-datum conclusion. |
| `solution_bound`, lines 49–55 | §8, lines 425–426. “Every body pair is an edge, so `ζ_tl + ω_tl = 2Ψ(t, l) + 2u_t + 2u_l ≤ 2M_0 + 2u_t + 2u_l`.” | The right side is the bound in D5′. `Chamber` is `W_n(τ)`, and `τ = 2n²` gives the case used there. The order `t < l` represents each unordered pair once. A single bound for D2 follows at fixed masses. |

## Field generality

For `a ≠ 0`, `v(a) + v(a⁻¹) = v(1) = 0`, so `v(a)` is finite. The valuation inequality for differences gives both ultrametrics. Symmetry cancels the internal pairs in each cut sum. The factor of two in `2v(P_tl) = −ζ_tl − ω_tl` comes from (N1) and is divided out in `ℝ`.

A proper nonempty cut has a nonzero crossing body term. The cut with all bodies has a nonzero origin term in each colour by (N1) and `n ≥ 2`. Each cut sum is zero. A unique least valuation would force the sum to have that finite valuation. This rules out a failed cut over any of the fields in the Lean statement.

For an explicit test, use `𝔽₂(T)` with the `T`-adic valuation. Take `n = 2`, `m = (T³(1 − T), T⁴)`, `X = Y = (T², T² − T)`, and `P_01 = P_10 = T⁻¹`. Both differences from body 0 to body 1 are `T`, so (N1) gives `T⁻² T² = 1`. The right sides of (N2) and (N3) are `T²` at body 0 and `−T(1 − T)` at body 1. Each of the three nonempty cuts has two terms of valuation 5 in each colour.

## Bound and nonemptiness

D4 gives `Ψ* = −q·u/N` with `|N| ≥ 3` and `|q_j| ≤ 2n − 1`. Thus `Ψ* ≤ M₀ = (2n − 1) Σ_j |u_j|/3`. The pair formula gives `v(X_tl Y_tl) = ζ_tl + ω_tl = 2Ψ(t, l) + 2u_t + 2u_l ≤ 2M₀ + 2u_t + 2u_l`. This is the bound at lines 53–55. For fixed masses, `M = 2M₀ + 4 max_j |u_j|` works for all solutions and pairs, as D2 requires at brief lines 205–207.

The same two-body formulas give a solution in the Hahn field. Its weights are `u = (3, 4) ∈ W_2(8)` and the bound reads `2 ≤ 28` for `(0, 1)`. This meets every premise. A trivial valuation gives an empty chamber.

## Issues

No replacements are needed.

## Scope

`lake env lean ChallengeA.lean` succeeded with `sorry` warnings for the placeholders at lines 44 and 55. The proof implementations, the validity of D4 and D2, and the rest of the finiteness argument were outside scope. `SolutionA.lean`, `DirectRoute/`, the README, and prior report and referee files were left unread.
