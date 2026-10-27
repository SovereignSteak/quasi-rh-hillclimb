# Limits from repeated bin ceiling updates

27 October 2026. Prepared by Codex (AI-assisted), building on Rohan Arun
and Claude's budget and Sagar Thakrar's [fixed ceiling analysis](side-constraint-limits.md).

The idealized budget with adaptive count `R = 1 - delta` can pass below
the earlier fixed `delta <= 3/4` limit if each successive step uses the
previous step's narrower bin range. Its sharp limiting boundary is

$$
\sigma_* = \frac{89309+\sqrt{2542433881}}{160200}
          = 0.872231918209182310720256\ldots.
$$

Every strictly feasible step starting from `7/8` remains above this value,
and strictly feasible rational steps approach it. The limit is not attained.
This is a proved statement about the specified finite budget. The hypothetical
adaptive count is not proved here, so these numbers are **not zero-free
endpoints**. Any analytic application remains conditional on the preprint's
`7/8` theorem, its applicable audit edits, and a uniform improved count.

## The budget and its variable ceiling

Keep the original geometry, low estimate, floor count, contour and twelve
side constraints from `certify.py`. Make precisely two changes:

1. Replace the adaptive high-row count by `R = 1 - delta`, while still
   checking its exponent on `0 <= delta <= 5/6`, `0 <= x <= 1/2`.
2. Check the intermediate count `76/75 - 2 delta/3` on
   `1/50 <= delta <= D`, replacing its fixed upper endpoint `5/6` by `D`.

The floor count remains `R = 1`, and the redundant high endpoint at
`delta = 5/6` stays in the side constraints. The geometry is

$$
\sigma=\frac{11}{12}-\frac\ell4,\quad
b=2h-1-3\ell,\quad l_y=h-2\ell,\quad l_x=1+\ell-h.
$$

For every `37/50 <= D <= 5/6`, the sharp infimum of this model is

$$
S(D)=\frac{71975D+38057}{36(2225D+1262)}.
$$

This recovers both earlier results exactly:

| Intermediate ceiling | Sharp infimum of the ideal budget |
| --- | --- |
| `D = 5/6` | `84031/96156` |
| `D = 3/4` | `368153/422028` |
| Repeated updates `D = 2u - 1` from the preceding boundary `u` | `(89309 + sqrt(2542433881))/160200` |

The fixed-ceiling results remain valid. Updating the ceiling changes their
hypotheses; the final row does not contradict either of them.

## Exact elimination and sharpness

The floor and upper intermediate margins are `A/150` and `B_D/300`, where

$$
\begin{aligned}
A&=61-117\ell-50h,\\
B_D&=24-225\ell+98h+D(150h-450\ell-125).
\end{aligned}
$$

The positive combination

$$
(98+150D)A+50B_D
=2\{3589+1450D-(11358+20025D)\ell\}
$$

eliminates `h`. Strict positivity therefore forces `sigma > S(D)`.
The simultaneous zero has

$$
\ell_D=\frac{1450D+3589}{9(2225D+1262)},\qquad
h_D=\frac{4675D+1213}{2(2225D+1262)}.
$$

At this pair, each of the other ten side margins is strictly positive
throughout `37/50 <= D <= 5/6`. After clearing positive denominators,
their numerators are affine in `D`, so endpoint checks prove the assertion.
For the ideal adaptive margin, put `y = 1/2 - x`. Direct substitution gives

$$
-E_{\rm ideal}(h_D)=
\frac{5800D\delta y+35400D\delta+975D+
14356\delta y-22416\delta+885}{36(2225D+1262)}.
$$

Its numerator is affine in each variable separately. Positive values at
the eight corners of the `(D, delta, y)` box therefore prove positivity
everywhere. These are exact rational checks, not a numerical grid test.
The positive frequency slope `33/50 - delta/2` also controls frequencies
below `h` in this ideal adaptive model.

At the paper point `(1/6, 13/16)`, every side and the ideal adaptive margin
is strictly positive for the whole ceiling interval. For fixed `D`,
interpolate from `(ell_D, h_D)` towards that paper point. The margins are
affine in `(ell,h)`, apart from prime supply, whose multiplication by
positive `h` makes it affine too. Every interior interpolant is strictly
feasible. This proves sharpness, including rational parameters whenever
`D` and the interpolation weight are rational.

## Repeated updates without circular assumptions

Suppose the **incoming** boundary is `u`. Its bin ceiling is `D = 2u - 1`.
The next ideal budget has strict frontier

$$
f(u)=S(2u-1)=\frac{71975u-16959}{18(4450u-963)}.
$$

An outgoing boundary must be strictly greater than `f(u)`. It is not
legitimate to assume the outgoing zero-free region when checking that step.
The rational witnesses below all use the incoming ceiling.

The fixed-point identity is

$$
u-f(u)=\frac{80100u^2-89309u+16959}{18(4450u-963)}.
$$

Its larger root is `sigma_*`. Exact sign checks isolate it between
`0.8722319182091823` and `0.8722319182091824`. On
`sigma_* < u <= 7/8`, the map is increasing and satisfies
`sigma_* < f(u) < u`. Its derivative is

$$
f'(u)=\frac{2051875}{6(4450u-963)^2},\qquad 0<f'(u)<\frac1{20}.
$$

Consequently, the strictly feasible choice `u_next = (u + f(u))/2`
decreases to `sigma_*`. For every step, interpolation in the preceding
section supplies its height. Starting from rational `u = 7/8` gives
rational parameters at every finite step. Continuity and the fixed-point
identity establish convergence; the root is never used as an attained
strict certificate.

There is also a direct obstruction for the model whose ceiling is set
equal to its own boundary, `D = 2sigma - 1 = 5/6 - ell/2`:

$$
(98+150D)A+50B_D
=\frac{60075\ell^2-172623\ell+28784}{3}.
$$

The retained floor and `b > 0` imply `A + 25b = 36 - 192ell > 0`,
so an improvement over `7/8` has `1/6 < ell < 3/16`. On this interval
the quadratic above is strictly decreasing and has just one root,
`ell_* = (57541 - sqrt(2542433881))/40050`. Thus every feasible point
requires `ell < ell_*`, equivalently `sigma > sigma_*`. This excludes
the remote second algebraic root. The incoming-ceiling construction also
passes the narrower outgoing intermediate interval, proving sharpness
for this model as well.

## Exact experiments and reproduction

The certificate generates twelve rational steps using upward decimal
rounding strictly above `f(u)`; it checks every step against its incoming
ceiling. Selected outputs are:

| Step | Strictly feasible boundary in the ideal budget |
| --- | --- |
| 1 | `0.872344` |
| 2 | `0.8722366` |
| 4 | `0.872231928` |
| 8 | `0.8722319182094` |
| 12 | `43611595910459117/50000000000000000 = 0.87223191820918234` |

All heights, interpolation weights, side margins and full-rectangle
adaptive lower bounds are in the [exact receipt](bootstrap-side-limits-evidence/certificate.json).
At `sigma = 0.87223`, the obstruction polynomial is exactly
`-29016213/25000000`, making the two required positive margins impossible
for **every** `h`. This is an infeasibility proof, not a failure to find a
Bernstein certificate. Conversely, the original adaptive count fails at
the final strict ideal witness, as checked at `(delta,y) = (2/5,0)`.

Run with the repository's existing SymPy dependency:

```sh
python3 auto-research/certify_bootstrap_side_limits.py
python3 auto-research/certify_bootstrap_side_limits.py --json /tmp/bootstrap-receipt.json
```

The checks derive the margins from the existing `certify.high_exponent`,
prove identities and signs exactly, and refuse Python's `-O` mode.
Decimal approximations are display only. The receipt includes source
hashes and runtime versions. The original certifier and defaults are unchanged.

## Sources and remaining analytic obligations

Repository base: `10d1b8031dc6d1e293db6089e4a7a8f5a76af3d9`.
The prior fixed-ceiling result is [PR #17](https://github.com/rohanarun/quasi-rh-hillclimb/pull/17).
The [upstream snapshot](bootstrap-side-limits-evidence/upstream-snapshot.json)
records that tracker [PR #84](https://github.com/GTimG/QuasiRiemannTracker/pull/84)
merged on 27 October with declared Dirichlet boundary `174797/200000 = 0.873985`.
That newer proof was not replayed here and supplies no premise to this analysis.
All preprint references use `openai/math` commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, `build/paper.tex`,
blob `268c4e3206d460c617d3d2129742a72b831b3def`:

| Source lines | Role |
| --- | --- |
| [6812–6830](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L6812) | Physical bin ceiling `delta <= 2 beta_* - 1`. |
| [6857–6866](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L6857) | Original probe geometry, generalized by this repository's budget. |
| [12559–12573](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L12559) | The fixed admissible moment parameter `kappa = 3/4` remains conservative under stronger incoming bounds. |
| [15726–15736](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L15726) | First-line high exponent used by `certify.high_exponent`. |
| [15843–15851](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L15843) | Unchanged floor treatment. |
| [16146–16165](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L16146) | Unchanged intermediate count and endpoint argument. |

An analytic iteration would need a proved uniform adaptive count and an
updated continuation argument at **every finite step**, for all finite-order
Hecke characters entering `beta_*`. A bound stated only for Dirichlet
characters cannot silently replace that input. The Euler-region,
completed-row norm, contour and error obligations in
[AUDIT_SUMMARY.md](../AUDIT_SUMMARY.md) also remain. Margins shrink along
the sequence; each finite step must choose its error allowances after
fixing its positive margins.

To go below this model's limit, at least one of its floor estimate,
intermediate estimate or geometry must change. This obstruction does not
apply to arbitrary structural methods or to the separate source-moment
tracker frameworks. There is no Lean formalization or new analytic
estimate in this contribution.
