# Separate floor counts and sharp density targets

27 October 2026. Prepared with substantial Codex assistance, building on
OpenAI's preprint, Rohan Arun and Claude's exponent budget, Sagar Thakrar's
fixed-ceiling analysis, and [PR #29](https://github.com/rohanarun/quasi-rh-hillclimb/pull/29).

The intermediate count `76/75 - 2 delta/3` deliberately adds `1/75` so one
formula covers floor and nonfloor bins. The preprint already supplies
`1 - 2 delta/3` for nonfloor rows, while the existing floor inequality
separately covers the actual floor rows with `R = 1`. Removing the common
count's enlargement therefore requires no new density estimate. At the
intermediate endpoint `d = 1/2`, it gains exactly `1/150` in the margin.

With this split, PR #29's **ideal adaptive-count budget** has sharp infimum

$$
\sigma_{\mathrm{split}}
=\frac{89309+\sqrt{2534423881}}{160200}
=0.8717357171994976486564018\ldots.
$$

This improves the model limit `0.8722319182091823` from the retained common
count. The ideal adaptive input `R = 1 - delta` remains hypothetical.
No new zero-free bound or Lean endpoint follows: analytic interpretations
remain conditional on the preprint's `7/8` theorem and applicable audit edits.

## Floor rows remain separate

Actual floor labels `a = 51/100`, including downward-rounded zeros,
retain `R = 1` and `q <= 1/100`. Their positive frequency slope `67/100`
and the constructed `h > 1/2` let the existing bound cover all intermediate
frequencies. Nonfloor labels have a witness and the no-slot count
`R = 1 - 2 delta/3`, uniformly near the floor. Its frequency slope
`33/50 - delta/6` is positive; physical prime corrections still allow
`q <= delta/2`. Checking its closure `1/50 <= delta <= D` is conservative,
but never assigns this stronger count to actual floor rows.

## Exact frontier with the source count

Keep every other constraint and the ideal adaptive rectangle from PR #29.
Write `sigma = 11/12 - ell/4`. The floor margin is `A/150`, and the new
upper intermediate margin is `B_D/300`, where

$$
A=61-117\ell-50h,\qquad
B_D=26-225\ell+98h+D(150h-450\ell-125).
$$

Compared with PR #29, `B_D` increases by exactly two. Eliminating `h`
gives, for `71/96 <= D <= 5/6`, the sharp fixed-ceiling frontier

$$
S(D)=\frac{71975D+38007}{36(2225D+1262)}.
$$

The simultaneous-zero pair is

$$
\ell_D=\frac{1450D+3639}{9(2225D+1262)},\qquad
h_D=\frac{4675D+1187}{2(2225D+1262)}.
$$

The remaining side margins and full ideal adaptive rectangle are strictly
positive there. Clearing positive denominators gives polynomials affine
in each box variable; their corner signs provide exact global certificates.
Interpolation towards `(1/6,13/16)` gives strict feasibility approaching
the frontier, including rational parameters. Equality is not attained.

| Intermediate ceiling | Sharp ideal-budget infimum |
| --- | --- |
| `D = 5/6` | `587917/673092` |
| `D = 3/4` | `122651/140676` |
| Repeated incoming-ceiling updates | `(89309 + sqrt(2534423881))/160200` |

For incoming boundary `u`, use `D = 2u - 1`. The resulting map is

$$
f(u)=\frac{71975u-16984}{18(4450u-963)},\qquad
u-f(u)=\frac{80100u^2-89309u+16984}{18(4450u-963)}.
$$

Its larger fixed point is `sigma_split`. Choosing an outgoing boundary
strictly between `f(u)` and `u` constructs decreasing rational iterations
from `7/8` approaching that limit. Every step checks its **incoming**
ceiling; no outgoing zero-free region is assumed.

## The next density estimate and its saturation point

To quantify the remaining intermediate-row task, suppose hypothetically
that nonfloor rows admit `R = 1 - k delta`, with `2/3 <= k <= 1`.
Here `k` denotes the density slope, not the preprint's moment parameter.
Actual floor rows still have `R = 1`; ideal adaptive counts are unchanged.

For fixed `D`, the exact sharp frontier becomes

$$
\max\left\{\frac{167}{192},
\frac{(24825-1250k)D+12669}{12(2225D+1262)}\right\}.
$$

The transition occurs at `kcrit(D) = (1025D - 322)/(800D)`. Below it,
the floor/intermediate limiting pair is

$$
\ell_{D,k}=\frac{(1250k-350)D+1213}{3(2225D+1262)},\qquad
h_{D,k}=\frac{(5975-1950k)D+1187}{2(2225D+1262)}.
$$

This pair interpolates affinely, as `k` increases, from the source-count
pair to `(3/16,25/32)`. At and above the transition, that last pair sets
the frontier: the floor and `b > 0` constraints alone force
`A + 25b = 36 - 192ell > 0`, hence `sigma > 167/192`.
All other side and ideal adaptive margins remain nonnegative at the
limiting pairs and become strict upon interpolation towards the paper
point with `k` fixed. Thus both phases are sharp.

Under repeated incoming-ceiling updates, the phase threshold is exactly

$$
k_* = \frac{41863}{56800}=0.7370246478873239\ldots.
$$

For `2/3 <= k < k_*`, the infimum is the unique root in
`(167/192,7/8)` of

$$
26700u^2+(1250k-30603)u+6078-625k=0.
$$

For `k >= k_*`, the infimum is `167/192`. The capped bootstrap map is
increasing and has Lipschitz constant below `1/20`; strict interpolation
therefore approaches the appropriate fixed point without attaining it.
An exact intermediate target follows by substituting `u = 87/100`:

$$
P_k(87/100)=\frac{23125k-16869}{50}.
$$

Consequently, a strictly feasible ideal budget at `sigma = 0.87` requires
and permits **`k > 16869/23125`**. This is a precise target for a new
uniform nonfloor density estimate. Estimates with `k > 2/3` are not
proved here. Once `k_*` is reached, further intermediate-count improvements
cannot beat the retained floor and geometry obstruction.

## Reproduction and proof obligations

```sh
python3 auto-research/certify_split_floor_limits.py
python3 auto-research/certify_split_floor_limits.py --json /tmp/split-floor-receipt.json
```

The checker derives its inequalities from `certify.high_exponent`, checks
both phases globally using exact arithmetic, and constructs fifty strict
rational steps across five slope choices. It refuses Python's `-O` mode.
Its receipt includes rational margins, source hashes and runtime versions.
The [saved receipt](split-floor-limits-evidence/certificate.json) and
[replay log](split-floor-limits-evidence/replay.log) record the exact checks.
An exact negative combination excludes `sigma = 0.87173` at the source
slope and ceiling `D = 2sigma - 1`, for every height; the existing adaptive
count also fails at the final ideal witness.

For analytic use, choose losses and height allowances after fixing each
finite candidate's positive floor and nonfloor margins. No positive margin
uniform along an infinite limiting sequence is claimed. The variable
geometry, Euler-region, completed-row and continuation obligations remain,
as does a uniform improved adaptive estimate for all Hecke characters
entering the zero supremum. The original frozen Track A obstruction is
unchanged; this result sharpens the ideal structural model.

## Pinned source map

All preprint references use `openai/math` commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`,
blob `268c4e3206d460c617d3d2129742a72b831b3def`.

| Native source lines | Use |
| --- | --- |
| [4281–4323 and 4374–4383](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L4281) | Exact floor label, nonfloor witness and physical bin ceiling. |
| [4510–4543](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L4510) | Witness uniformity near the floor. |
| [15212–15219 and 15437–15446](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L15212) | No-slot nonfloor count and its derivation. |
| [15711–15756](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L15711) | High exponent and admissibility of separate count cases. |
| [15843–15851](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L15843) | Independent floor coverage. |
| [16146–16165](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L16146) | Explicit common-count enlargement removed here. |
