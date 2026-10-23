# Role-specific ordinary-source chains and a conditional theta = 0.87477137

**Status: proposal.** Subhanjan Das (@subhanjandas), substantially assisted
by OpenAI Codex. 23 October 2026. Exact finite premises pass; the changed
analytic endpoint is not Lean-verified or independently accepted.

## 1. Change

Extend the finite source graph in Hailey Collet's [PR #8](https://github.com/rohanarun/quasi-rh-hillclimb/pull/8),
using her unchanged generic NF source step and parameterized return.
Use separate chains for the count source and physical numerator:

| Role | Slope decrement per step | Global cap | Steps | Final `(B, Lambda)` |
|---|---:|---:|---:|---|
| Count | `1/2000` | `.044001` | 2691 | `(.96258631988264, 3.1518108)` |
| Physical | `1/1000` | `.043001` | 1220 | `(.96772063836150, 3.2773108)` |

Every LOW/HIGH parent is strictly earlier. The only initial face is the
inherited natural `G(1, 11243277/2500000, 11/200)`. The accounting remains
`(e,r,f)=(10^-17,10^-12,10^-10)`; the centered terminal saving remains `.499`.

No analytic lemma of the original preprint is strengthened or patched.
The directly affected interfaces are Collet's NF1/NF4/NF8/NF10–NF15 in
`paper/feedback.tex`, lines 254–430, and NR1–NR10 in `paper/return.tex`,
lines 10–147. They are pinned and mapped in [SOURCE_MAP.md](../role-source-caps/SOURCE_MAP.md).
For the requested original `build/paper.tex` map, the inherited compensated
row norm is at line 8111, the short-prime plain moment at 12531, and the
old balanced endpoint at 15994, at OpenAI revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. These are inherited context;
their old Track A certificate is not reused as a certificate for this point.

## 2. Needed statement

For every node in the new finite graph, establish the full inherited
ordinary-source assertion

\[
G(B,\Lambda,H):\quad
\mathcal E\ll U^{Q+\epsilon}\mathcal H_J,
\qquad m_1,m_2\ge0,\quad 0\le s\le HQ,\quad
m_1+m_2+\Lambda s\le BQ.
\]

Here `H` is the source cap, distinct from the return parameter `h`.
All fixed-data, canonical marked-pool, natural-zero, puncture, profile,
restoration and independently bounded height conditions are exactly those
of Collet's NF1/G1. This notation does not remove their quantifiers or
replace a uniform analytic assertion by a finite sample.

Then instantiate her full physical/Mellin return at

\[
\theta=87477137/10^8,\qquad h=1250109/1562500,\qquad
\ell=12568589/75000000,\quad x=27563357/75000000,\quad
y=17434027/37500000,\quad\kappa_*=37477137/50000000.
\]

The finite return target is

\[
\frac12+\frac{13h}{75}-\frac y2-\frac\ell2-
\frac9{100}d+\frac\delta2+
\delta p\left(\ell-\frac{C(d)}2\right)+
\frac{3d}{4}R_*(\kappa_*,\delta,p)
\le\theta-10^{-9},
\]

for `delta in [0,3/4]`, `p in [0,1/2]`, and every conductor interval from
`d0=1/200` to `d+=h+10^-10`, using NR4's old/new capacities and NR5's
fixed joins. The exact checker certifies the six endpoint covers,
admissions and scalar reserves. Completing the implication to the literal
analytic numerator, common meshes and final canonical endpoint remains
required. A new source-step or return assertion is not assumed as an axiom.

## 3. Payoff

Conditional on those inherited analytic interfaces applying with all
required hypotheses, the proposed nonvanishing boundary is

\[
\operatorname{Re}s>87477137/100000000=0.87477137,
\]

with the principal pole excluded. No unconditional new endpoint or tracker
record is asserted. The exact boundary reduction relative to Collet's
`.8747729897` is `16197/10^10`.

This is a different source/return budget from the frozen Track A model;
`whatif.py` is not used to infer this number. The attached modified budget
and exact certificate are reproduced by:

```sh
python auto-research/role-source-caps/replay.py
```

The symmetry-related critical-strip description would follow only after
the analytic endpoint and functional-equation application are established.
No additional interior zero-free band, `.86` bound or `.7x` bound is claimed.

## 4. Evidence and partial proof

The complete graph and regenerated receipt check 3,911 acyclic stages,
125,152 strict scalar gates, 7,822 weak LOW-cap guards and 70,398 cubic
density positivity tests, each cross-checked by independent interpolation.
The return checks 224 boxes, 2,688 coefficients, 49 admission windows and
33 scalar reserves. Every test is rational; floating search only generated
candidates. The two actual cap reserves are each `10^-6`.

The code also reproduces the old return and compares all 2,688 normalized
coefficients with Collet's archived Lean sources. This checks the
transcription at the old point; it does not formally verify the changed
point. Negative controls reject invalid source dependencies and incomplete
or duplicated covers, and optimized Python is rejected explicitly.

The finite proof mechanism is affine interpolation in width, positive cubic
Bernstein coefficients in density, tensor Bernstein positivity on return
rectangles, and the inherited piecewise-affine conductor interpolation.
See the [readable account](../role-source-caps/README.md),
[verification scope](../role-source-caps/VERIFICATION.md) and
[research log](../role-source-caps/RESEARCH_LOG.md).

## 5. What breaks, downstream changes and next steps

The count/physical source constants, actual caps, return height and theta
change. Therefore source admissions, source restrictions, return
polynomials, the closed cover and every geometry reserve must be
recomputed; the old point's positivity or generic headline audit is
insufficient. Those finite computations are supplied.

The unfinished formal tasks are the new admitted-window constructors,
full cover and all-conductor bounds, `PhysicalSchedule`, common-mesh
literal numerator and canonical nonvanishing theorem, followed by
transitive axiom audits and fresh kernel replay. An optional uncompiled
Lean source exporter is supplied as a handoff, not proof evidence.

The larger mixed off-diagonal estimate remains open. The exploratory
coefficient, profile and Mellin routes in the research log are not premises
of this candidate. Finite numerical reductions do not yield asymptotic
power savings. No optimality or universal method ceiling is established.

New integration is MIT; Collet/OpenAI and all inherited author/license
notices remain. Codex substantially assisted mathematics, code, checking
and writing. Independent mathematical review is outstanding.
