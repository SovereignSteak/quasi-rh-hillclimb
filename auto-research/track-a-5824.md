# Track A: an exact certificate at N = 5824

Date: 2026-10-22. Prepared by Codex (AI-assisted), using Rohan Arun and
Claude's existing budget, search tool, Bernstein certifier, and audit.
Repository starting revision: `e4cf5a2b1f967746b36606d3352549ee598e373f`.

## Result and scope

The final-section inequalities certify at

\[
\ell=\frac16+\frac1{5824}=\frac{2915}{17472},\qquad
h=\frac{405967}{500000},\qquad
\sigma_0=\frac{20383}{23296}=\frac78-\frac1{23296}.
\]

This lowers the previous N = 5826 final-section boundary by exactly
`1/67861248` (approximately `1.47359506e-8`). It is a parameter refinement
within the existing architecture. It is **conditional on the preprint's
7/8 theorem and the edits in [AUDIT_SUMMARY.md](../AUDIT_SUMMARY.md)**.
The certificate proves the arithmetic implemented by `certify.py`, not a
complete nonvanishing theorem or a Lean endpoint. The original audited
point remains N = 5900. The separate source-moment and Lean tracker results
are stronger than this Track A result.

The [audit-formula follow-up](track-a-audit-formulas.md) identifies the
affected preprint lines, recomputed margins, and remaining proof obligations.
Old audit reports and historical result rows are unchanged.

## Reproduction

From the repository root, with `numpy`, `scipy`, and `sympy` installed:

```sh
python auto-research/hillclimb.py --start 5825 --stop 5824 --step 1 --maxdepth 24
python certify.py 5824 405967/500000
```

The first command finds the candidate using floating-point search and then
certifies it with rational arithmetic. Only the second step is evidence of
positivity. The standalone command produces:

```text
ell = 2915/17472  h = 405967/500000  ->  sigma0 = 20383/23296 = 7/8 - 1/23296  (~0.87495707)
check paper point: sigma0(1/6) = 7/8
J>0 on box: True
adaptive endpoint F>0 on delta in [0,5/6], y in [0,1/2]: True  (26 boxes)
   smallest Bernstein lower bound among boxes: 2.466e-06
   OK  floor bin (delta0=1/50, R=1, q=delta0/2): -E(h): 82433/14000000 (~0.00589)
   OK  delta=5/6 endpoint (R=1-delta, q=delta/2): -E(h): 19735241/273000000 (~0.07229)
   OK  intermediate d=1/2, delta=1/50: 18802337/87500000 (~0.21488)
   OK  intermediate d=1/2, delta=5/6: 108052493/40950000000 (~0.00264)
   OK  small rows: -(h(z0-1/6) - l_y/2 + 2 d_min): 267517489/3412500000 (~0.07839)
   OK  prime supply at d=h: ell/h - 7/37: 133628501/8201345334 (~0.01629)
   OK  extension room: 5 ell - h (paper uses zeta < 5ell-h): 6076393/273000000 (~0.02226)
   OK  b > 0: 11225113/91000000 (~0.12335)
   OK  low side: l_x - ell: 94033/500000 (~0.18807)
   OK  low side: l_y - ell - 11b/6: 46558471/546000000 (~0.08527)
   OK  low side: M - 2 ell = 1 - 3 ell: 2909/5824 (~0.49948)
   OK  high margin coefficient 1 - h/4: 1594033/2000000 (~0.79702)
paper point (1/6, 13/16) certifies: True
```

The original maximum depth of 20 returned `False` after certifying only
seven boxes. Increasing it to 24 completes a 26-box partition. This is the
only change to `certify.py`; its polynomial, constraints, Bernstein
conversion, and strict positivity test are unchanged. The search tool
still accepts its own explicit `--maxdepth` argument.

The minimum Bernstein coefficient across the completed partition is exactly
`564781781/229008998400000 > 0`. For the second polynomial returned by
`adaptive_poly`, namely **108 times the denominator J**, the global
Bernstein lower bound is `70 > 0` and its upper bound is `270`. Thus
division by the denominator is valid, and on the whole rectangle

\[
-E_* \ge \frac{564781781}{61832429568000000}>0.
\]

This supplies a replacement for the paper's old explicit adaptive margin;
the old `49/440640` must not be carried over to this geometry.

The following assert-based check reproduces those exact values and checks
that an explicitly invalid neighboring point is rejected:

```sh
python - <<'PY'
from fractions import Fraction as Fr
import sympy as sp
import certify as C

ell = Fr(1, 6) + Fr(1, 5824)
h = Fr(405967, 500000)
box = ((sp.Rational(0), sp.Rational(5, 6)),
       (sp.Rational(0), sp.Rational(1, 2)))
F, J108 = C.adaptive_poly(ell, h)
log = []
assert C.prove_positive(F, box, log=log)
assert len(log) == 26
assert min(bound for _, bound in log) == sp.Rational(564781781, 229008998400000)
assert C.bernstein_min(J108, box) == 70
assert -C.bernstein_min(-J108, box) == 270
assert all(value > 0 for value in C.side_constraints(ell, h).values())

# An exact negative value, not merely exhausted bisection, rejects this point.
Fbad, _ = C.adaptive_poly(Fr(1, 6) + Fr(1, 5823), h)
witness = Fbad.as_expr().subs({C.d: sp.Rational(194323, 500000), C.y: 0})
assert witness == -sp.Rational(33322263931253, 15164062500000000000)
assert witness < 0
assert not C.prove_positive(Fbad, box)
print('Exact certificate and negative control passed.')
PY
```

The negative control excludes only N = 5823 **at this h**. It is not a
proof of an optimal parameter or a ceiling over all h.

## Validation

Executed with Python 3.13.5, SymPy 1.14.0, NumPy 2.5.4, and SciPy 1.18.1:

- N = 5824: denominator and adaptive checks `True`, all 12 side checks `OK`.
- Prior N = 5826: adaptive check `True` on 22 boxes, all 12 side checks `OK`.
- Audited N = 5900: adaptive check `True` on 18 boxes, all 12 side checks `OK`.
- The preprint point `(1/6, 13/16)` certifies in each standalone run.
- The exact negative witness above is negative and its candidate is rejected.

No Lean build, full preprint re-audit, or patched `paper.tex` is claimed.
