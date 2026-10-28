# Fourth density transitions at a conditional boundary of 0.873981

27 October 2026. Prepared with substantial Codex assistance. Builds on
Sil's density-split construction, Rohan Arun's third transition in tracker
PR #84, and the inherited work of OpenAI, Hailey Collet and ArviFoxy.

**Status: exact scalar certificates and Lean verification complete; tracker review pending.**
The conditional boundary is `theta = 873981/1000000 = 0.873981`, at
`h = 16109/20000` with return reserve `1/100000000`. This is exactly
`1/250000` below the parent submission's declared `174797/200000 = 0.873985`.
The source, admission, geometry and return inequalities pass exact arithmetic
checks. Their formal integration is in [tracker PR #85](https://github.com/GTimG/QuasiRiemannTracker/pull/85),
whose [verification run](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/40622628467)
accepted the canonical Comparator and all three kernels. All implications remain
conditional on the preprint's `7/8` theorem. The tracker PR is not merged.
Independent [tracker PR #86](https://github.com/GTimG/QuasiRiemannTracker/pull/86)
has since passed admission with a stronger 0.8739558 boundary via a finer chain.

The self-contained [replay bundle](../fourth-density-step/README.md)
contains the checkers, exact receipts, source pins, numerical search
diagnostics and the historical implementation handoff.

## Change and required source statements

Use the parent source `G(99/100, 239/100, 1/10)`. A source face has
boundary `P + Lambda*S <= B`, with `S <= c`. Add two separate applications
of the same variable-density step:

| Role | B | Lambda | c | A | D | Crossing with parent |
| --- | --- | --- | --- | --- | --- | --- |
| Physical numerator | `49461297/50000000` | `23767/10000` | `1/10` | `27/50` | `94` | `291/5000` |
| Additional count source | `987987/1000000` | `2357/1000` | `1/10` | `103/200` | `23` | `61/1000` |

The gates certify these two proposed transitions from the parent; neither
child is used as the other's premise. Retain the parent wherever its
face is stronger. For orientation, the physical face improves `B-Lambda*S`
by exactly `1197/50000000` at `S=3/50`, and the count face improves it by
`297/1000000` at `S=7/100`.

The analytic step is inherited from the pinned tracker source, not a new
preprint estimate. Its scalar interface is
[`Source/HybridGates.lean`](https://github.com/GTimG/QuasiRiemannTracker/blob/71996e7e79840455f7beead063a73b7b31cfb586/submissions/density-split-third-20261026/src/Submissions/density_split_third_20261026/Source/HybridGates.lean#L114).
The existing source assembly is
[`Source/Assembly.lean`](https://github.com/GTimG/QuasiRiemannTracker/blob/71996e7e79840455f7beead063a73b7b31cfb586/submissions/density-split-third-20261026/src/Submissions/density_split_third_20261026/Source/Assembly.lean).
The bundle records the generic provider and leaf declarations that must
be instantiated for these two new faces. Analytic interpretation retains
the preprint's `7/8` input and the inherited source and return theorems.

## Exact return and a necessary separation of roles

Use the physical child for the numerator schedule, restricted to source
cap `31/500`, with marked width cap `3/50`. Keep the parent's capped-count
branch and its ordinary count branch, and add the count child restricted
to `9999/100000`.

This distinction matters in Lean: the parent return shares
`physicalB` and `physicalLambda` between the physical schedule and its
`capP` count branch. Replacing those literals everywhere would describe
different count windows from the certified ones. The integrated implementation
gives the retained capped-count source its own parent constants.

The return certificate checks 29 upward admission windows and all four
conductor edges on 91 rectangles covering
`0 <= delta <= 3/4`, `0 <= p <= 1/2`. It also checks the old count
denominator, the geometry and capacity inequalities, and the identities
needed by the inherited scalar interface. Every positivity decision is
rational; the numerical optimizer only selected candidates.

The height choice is consequential. An earlier trial with
`theta = 0.873982` and `h = 0.8059` passed the row and admission tests but
failed the inherited floor margin by exactly
`-428480201/3000000000000`. It is retained as a negative control.
The final candidate uses the parent's original height `0.80545` and
passes that margin with reserve `12159799/3000000000000`.

## Lean integration completed

[Tracker PR #85](https://github.com/GTimG/QuasiRiemannTracker/pull/85) implements
the original handoff: both source gate instances and generic analytic providers,
a common admissible mesh for the parent and both children, separate retained
parent capped-count constants, the additional count branch, exact admission and
edge certificates, and the all-moduli endpoint. The renamed source compiled
with Lean 4.34.1 (13,403 jobs); `Candidate.bound` uses only `propext`,
`Classical.choice`, and `Quot.sound`. The tracker's proof worker accepted the
canonical Comparator and all three kernels for this exact PR head. Review and
merge are pending. The numerical optimum near `0.87398079` remains a diagnostic
only; the proved conditional boundary here is `0.873981`.
