# constraint-gap-lean

A machine check of the constraint-gap algebra in Egemen Tuncarslan's
Proposal A, Section 3 (adversarial attacks on WiFi CSI sensing under a
realizable-perturbation constraint).

Lean 4 against mathlib `v4.32.2`. Seven theorems, no `sorry`.

## What it establishes

Let `E` be a real inner product space, `V ≤ E` the subspace the attacker can
realize, `P = V.starProjection` its orthogonal projection, `g` the loss
gradient, `eps` the budget. "Locally linear with gradient `g`" means the
objective is `x ↦ ⟪g, x⟫`.

**Theorems 1–4 confirm the proposal's algebra as written.**

| # | name | statement |
|---|---|---|
| 1 | `inner_g_proj` | `⟪g, P g⟫ = ‖P g‖²` — the only real work; the rest follows fairly mechanically |
| 2 | `gain_project` | optimize-then-project: step `eps·Pg/‖g‖`, gain `eps·‖Pg‖²/‖g‖` |
| 3 | `gain_constrained` | optimize-under-constraint: step `eps·Pg/‖Pg‖`, gain `eps·‖Pg‖` |
| 4 | `gain_ratio` | the ratio is `cos θ = ‖Pg‖/‖g‖`, so the relative gap is `1 − cos θ` |
| — | `cos_le_one` | `‖Pg‖ ≤ ‖g‖`, so the gap is nonnegative |

**Theorems 5–6 are the observation the proposal does not make**, and they are
the reason the comparison in Section 3 needs reframing.

| # | name | statement |
|---|---|---|
| 5 | `projected_step_norm` | the projected step has norm `eps·cos θ`, so it **never spends the budget** whenever the gradient leaves `V` |
| 6 | `rescaled_projection_eq_constrained` | rescaling that step back to length `eps` returns **exactly** the constrained optimum |

Theorem 6 is an equality of *vectors*, not of norms. So in the locally linear
regime the gap of Theorems 2–4 measures the cost of failing to renormalise
after projecting, not a property of the constraint. Any method whose step has
full budget length closes it to zero, and iterated projected gradient descent
converges to the constrained optimum for the same reason.

## Why the closed form survives anyway

The same `1 − cos θ` holds for a different and more useful comparison: the
unconstrained attack (`eps·‖g‖`) against the best *realizable* attack
(`eps·‖Pg‖`). That ratio is again `cos θ`, and the gap is again `1 − cos θ` —
now measuring the fraction of attack power the physical constraint destroys,
which is the quantity the geometry was meant to explain. Same formula, changed
referent, and no longer contingent on the baseline being implemented badly.

## Building

```bash
lake exe cache get
lake build
```

If it does not build against mathlib `v4.32.2`, that is a bug in this
repository rather than in your setup — please open an issue.

`lake-manifest.json` pins every dependency to the revisions of the checked
build (mathlib `905b95818eb3`, tag `v4.32.2`). To confirm that nothing rests
on `sorry` or an added axiom:

```bash
lake env lean Axioms.lean
```

Each of the seven theorems should report only `propext`, `Classical.choice`
and `Quot.sound`, the standard axioms mathlib itself uses. Checked
2026-09-30 for v1.0.0, the version the WCNC 2027 manuscript cites.

## Reading order

Start at Theorem 6; it is short and the reframing rests on it. Then
`inner_g_proj`, which is what everything else is built from.

## The companion measurement suite

The measurements this algebra is checked against live in Egemen B.
Tuncarslan's repository, `egeboy35/constraint-gap-measurements` (private).
That is where the CSI datasets, the attack tools and the `cos theta`
experiments are; this repository holds only the formalization.

The two are archived to Zenodo separately at submission, with version DOIs, so
each is citable at the state the reported numbers came from.

Worth recording here, because it bears on Theorems 1 and 6: the applied
projection in the measurement suite is built by `tangent_basis`, which
orthonormalises the Jacobian's columns. It was verified orthogonal in Sep 2026
— idempotency `4.7e-16`, self-adjointness `1.2e-15`, principal cosines with
`col(J)` at 1.000000 — so the hypothesis these theorems need is satisfied by
what actually runs. The larger idempotency residual quoted earlier in
correspondence (`1.14`) belongs to the raw Jacobian, which is not the operator
applied.
