"""Exact side-constraint limits with a variable, then bootstrapped, bin ceiling.

Run: python auto-research/certify_bootstrap_side_limits.py
Optional: --json PATH writes the checked formulas and rational witnesses.

This proves statements about an idealized finite budget with adaptive R=1-delta.
It supplies neither that analytic count nor a new zero-free theorem. See
bootstrap-side-limits.md for the proof, source map, and conditional scope.
"""

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import certify as C


Q = sp.Rational
ELL, HEIGHT, UPPER, BOUND, TAU = sp.symbols("ell h D u tau")
FLOOR = "floor bin (delta0=1/50, R=1, q=delta0/2): -E(h)"
INTERMEDIATE = "intermediate d=1/2, delta=5/6"
CAP_INTERVAL = (Q(37, 50), Q(5, 6))
PAPER = {ELL: Q(1, 6), HEIGHT: Q(13, 16)}
RADICAND = 2542433881
ROOT = sp.sqrt(RADICAND)
SIGMA_STAR = (89309 + ROOT) / 160200
ELL_STAR = (57541 - ROOT) / 40050


def identity(left, right=0):
    assert sp.cancel(sp.expand(left - right)) == 0, (left, right)


def positive_multiaffine(expression, intervals):
    """Exact positivity on a box: a multi-affine polynomial is a corner mean."""
    variables = tuple(intervals)
    poly = sp.Poly(sp.expand(expression), *variables)
    assert not poly.as_expr().has(sp.Float)
    assert all(poly.degree(v) <= 1 for v in variables)
    values = [poly.as_expr().subs(dict(zip(variables, corner)))
              for corner in product(*intervals.values())]
    assert all(value.is_Rational and value > 0 for value in values), values
    return min(values)


def positive_rational(expression, intervals):
    numerator, denominator = sp.fraction(sp.cancel(expression))
    positive_multiaffine(denominator, intervals)
    return positive_multiaffine(numerator, intervals)


def build_model():
    sides = C.side_constraints(ELL, HEIGHT)
    assert len(sides) == 12
    intermediate = -C.high_exponent(
        ELL, HEIGHT, UPPER, UPPER / 2,
        Q(76, 75) - 2 * UPPER / 3, Q(1, 2))
    identity(intermediate.subs(UPPER, Q(5, 6)), sides[INTERMEDIATE])
    sides[INTERMEDIATE] = intermediate
    ideal = sp.expand(-C.high_exponent(
        ELL, HEIGHT, C.d, (Q(1, 2) - C.y) * C.d, 1 - C.d, HEIGHT))
    return sides, intermediate, ideal


def prove_family(sides, intermediate, ideal):
    a = 61 - 117 * ELL - 50 * HEIGHT
    b = 24 - 225 * ELL + 98 * HEIGHT + UPPER * (150 * HEIGHT - 450 * ELL - 125)
    identity(150 * sides[FLOOR], a)
    identity(300 * intermediate, b)
    elimination = 2 * (3589 + 1450 * UPPER - (11358 + 20025 * UPPER) * ELL)
    identity((98 + 150 * UPPER) * a + 50 * b, elimination)
    positive_multiaffine(98 + 150 * UPPER, {UPPER: CAP_INTERVAL})

    lstar = (1450 * UPPER + 3589) / (9 * (2225 * UPPER + 1262))
    hstar = (4675 * UPPER + 1213) / (2 * (2225 * UPPER + 1262))
    frontier = (71975 * UPPER + 38057) / (36 * (2225 * UPPER + 1262))
    star = {ELL: lstar, HEIGHT: hstar}
    identity(elimination.subs(ELL, lstar))
    identity(frontier, Q(11, 12) - lstar / 4)
    for value in (lstar - Q(1, 6), hstar):
        positive_rational(value, {UPPER: CAP_INTERVAL})

    segment = {v: TAU * PAPER[v] + (1 - TAU) * star[v] for v in PAPER}
    for name, side in sides.items():
        # Positive h removes the sole parameter denominator.
        if name.startswith("prime supply"):
            side = sp.cancel(HEIGHT * side)
        assert sp.Poly(side, ELL, HEIGHT).total_degree() <= 1
        at_star, at_paper = side.subs(star), side.subs(PAPER)
        if name in (FLOOR, INTERMEDIATE):
            identity(at_star)
        else:
            positive_rational(at_star, {UPPER: CAP_INTERVAL})
        positive_rational(at_paper, {UPPER: CAP_INTERVAL})
        identity(side.subs(segment), TAU * at_paper + (1 - TAU) * at_star)

    rectangle = {C.d: (Q(0), Q(5, 6)), C.y: (Q(0), Q(1, 2))}
    positive_rational(ideal.subs(star), {UPPER: CAP_INTERVAL, **rectangle})
    positive_multiaffine(ideal.subs(PAPER), rectangle)
    identity(ideal.subs(segment),
             TAU * ideal.subs(PAPER) + (1 - TAU) * ideal.subs(star))
    # Ideal high exponents increase with frequency, so d=h controls d<=h.
    positive_multiaffine(1 - C.d / 2 - Q(17, 50), rectangle)

    known = [(Q(5, 6), Q(84031, 96156)),
             (Q(3, 4), Q(368153, 422028))]
    for ceiling, sigma in known:
        identity(frontier.subs(UPPER, ceiling), sigma)
    print("PASS: variable-ceiling elimination and sharpness for 37/50 <= D <= 5/6")
    print("  S(D) = (71975 D + 38057) / (36 (2225 D + 1262))")
    print("  two limiting margins vanish; the other ten and ideal adaptive margin are positive")
    print("  strict rational interpolation passes all twelve sides and the full ideal rectangle")
    return lstar, hstar, frontier


def prove_bootstrap(frontier, sides):
    f = sp.factor(frontier.subs(UPPER, 2 * BOUND - 1))
    identity(f, (71975 * BOUND - 16959) / (18 * (4450 * BOUND - 963)))
    polynomial = 80100 * BOUND**2 - 89309 * BOUND + 16959
    identity(BOUND - f, polynomial / (18 * (4450 * BOUND - 963)))
    identity(polynomial.subs(BOUND, SIGMA_STAR))
    identity(SIGMA_STAR, Q(11, 12) - ELL_STAR / 4)

    # Isolate the larger root using rational signs and monotonicity only.
    low = Q(8722319182091823, 10**16)
    high = Q(8722319182091824, 10**16)
    assert polynomial.subs(BOUND, low) < 0 < polynomial.subs(BOUND, high)
    positive_multiaffine(sp.diff(polynomial, BOUND), {BOUND: (Q(167, 192), Q(7, 8))})
    assert Q(87, 100) < low < high < Q(7, 8)
    assert CAP_INTERVAL[0] < 2 * low - 1 < 2 * high - 1 < Q(3, 4)

    # The floor and b>0 exclude the remote second root, even for D below 37/50.
    a = 150 * sides[FLOOR]
    width = 2 * HEIGHT - 1 - 3 * ELL
    identity(a + 25 * width, 36 - 192 * ELL)
    obstruction = 60075 * ELL**2 - 172623 * ELL + 28784
    b = 300 * sides[INTERMEDIATE]
    weighted = (98 + 150 * UPPER) * a + 50 * b
    identity(weighted.subs(UPPER, Q(5, 6) - ELL / 2), obstruction / 3)
    identity(obstruction.subs(ELL, ELL_STAR))
    positive_multiaffine(-sp.diff(obstruction, ELL), {ELL: (Q(1, 6), Q(3, 16))})
    assert obstruction.subs(ELL, Q(1, 6)) > 0 > obstruction.subs(ELL, Q(3, 16))

    derivative = sp.factor(sp.diff(f, BOUND))
    identity(derivative, 2051875 / (6 * (4450 * BOUND - 963)**2))
    # Positive increasing denominator bounds f' throughout this interval.
    positive_multiaffine(4450 * BOUND - 963, {BOUND: (Q(87, 100), Q(7, 8))})
    assert 0 < derivative.subs(BOUND, Q(87, 100)) < Q(1, 20)
    print("PASS: bootstrap fixed point, exact root isolation, and excluded second root")
    print("  sigma > (89309 + sqrt(2542433881)) / 160200")
    print(f"  exact enclosure: {low} < sigma_* < {high}")
    print("  S(2u-1) < u for sigma_* < u <= 7/8; 0 < derivative < 1/20")
    print("  the strict iteration (u + S(2u-1))/2 converges to sigma_*")
    return f, low, high


def rational_witnesses(f, lstar, hstar, sides, ideal):
    """Twelve strictly feasible steps; rounding is outward and wholly rational."""
    current = Q(7, 8)
    rows = []
    for step in range(12):
        ceiling = 2 * current - 1
        edge = f.subs(BOUND, current)
        scale = 10**(6 + step)
        following = Q(sp.ceiling(edge * scale) + 1, scale)
        assert edge < following < current
        ll = Q(11, 3) - 4 * following
        ls, hs = lstar.subs(UPPER, ceiling), hstar.subs(UPPER, ceiling)
        tau = sp.cancel((ls - ll) / (ls - Q(1, 6)))
        assert 0 < tau < 1
        hh = sp.cancel(tau * Q(13, 16) + (1 - tau) * hs)
        point = {ELL: ll, HEIGHT: hh, UPPER: ceiling}
        margins = {name: sp.cancel(value.subs(point)) for name, value in sides.items()}
        assert all(value.is_Rational and value > 0 for value in margins.values())
        bound = positive_multiaffine(ideal.subs(point),
                                    {C.d: (Q(0), Q(5, 6)), C.y: (Q(0), Q(1, 2))})
        # Check the narrower outgoing domain too; this does not assume its theorem.
        outgoing_margin = sp.cancel(sides[INTERMEDIATE].subs(
            {ELL: ll, HEIGHT: hh, UPPER: 2 * following - 1}))
        assert outgoing_margin > 0
        rows.append({"step": step + 1, "incoming_bound": str(current),
                     "incoming_delta_cap": str(ceiling), "strict_frontier": str(edge),
                     "sigma": str(following), "ell": str(ll), "h": str(hh),
                     "tau": str(tau), "ideal_adaptive_lower_bound": str(bound),
                     "outgoing_intermediate_margin": str(outgoing_margin),
                     "side_margins": {k: str(v) for k, v in margins.items()}})
        current = following
    print(f"PASS: {len(rows)} strictly feasible rational bootstrap witnesses (ideal budget only)")
    print(f"  final rational sigma = {current}; all sides and the full ideal rectangle pass")
    return rows


def negative_controls(lstar, hstar, frontier, root_upper, witnesses):
    # Point at a plausible target below the claimed infimum is truly impossible:
    # the positive combination of the floor and intermediate margins is negative.
    bad_sigma = Q(87223, 100000)
    bad_ell = Q(11, 3) - 4 * bad_sigma
    obstruction = 60075 * bad_ell**2 - 172623 * bad_ell + 28784
    assert obstruction < 0
    # An actual adaptive-count witness distinguishes the idealization from Track A.
    ll, hh = lstar.subs(UPPER, Q(3, 4)), hstar.subs(UPPER, Q(3, 4))
    actual, denominator = C.adaptive_poly(ll, hh)
    location = {C.d: Q(2, 5), C.y: Q(0)}
    value = actual.as_expr().subs(location)
    assert value < 0 < denominator.as_expr().subs(location)
    assert frontier.subs(UPPER, Q(3, 4)) > root_upper
    last = witnesses[-1]
    final_actual, final_denominator = C.adaptive_poly(Q(last["ell"]), Q(last["h"]))
    final_value = final_actual.as_expr().subs(location)
    assert final_value < 0 < final_denominator.as_expr().subs(location)
    print("PASS: exact infeasibility witness at sigma=0.87223, independent of h")
    print("PASS: the present adaptive count rejects the idealized D=3/4 limiting pair")
    print("PASS: the present adaptive count also rejects the final strict ideal witness")
    return {"infeasible_sigma": str(bad_sigma), "obstruction_polynomial": str(obstruction),
            "actual_adaptive_F_at_ideal_pair": str(value),
            "actual_adaptive_F_at_final_witness": str(final_value)}


def main():
    if not __debug__:
        raise SystemExit("Exact checks require assertions; run Python without -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write an exact arithmetic receipt")
    args = parser.parse_args()
    sides, intermediate, ideal = build_model()
    lstar, hstar, frontier = prove_family(sides, intermediate, ideal)
    f, low, high = prove_bootstrap(frontier, sides)
    witnesses = rational_witnesses(f, lstar, hstar, sides, ideal)
    controls = negative_controls(lstar, hstar, frontier, high, witnesses)
    receipt = {"schema": "quasi-rh-ideal-side-bootstrap-v1", "status": "proved finite-budget statement",
               "scope": "Hypothetical adaptive R=1-delta; no analytic count or zero-free theorem proved",
               "sigma_infimum": "(89309 + sqrt(2542433881))/160200",
               "strict_root_enclosure": [str(low), str(high)],
               "frontier": str(frontier), "bootstrap_map": str(f),
               "family_delta_interval": list(map(str, CAP_INTERVAL)),
               "source_sha256": {"certify.py": hashlib.sha256(Path(C.__file__).read_bytes()).hexdigest(),
                                 Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
               "environment": {"python": sys.version.split()[0], "sympy": sp.__version__},
               "witnesses": witnesses, "negative_controls": controls}
    if args.json:
        args.json.write_text(json.dumps(receipt, indent=2) + "\n")
    print("Displayed approximation only:", sp.N(SIGMA_STAR, 26))
    print("All proof decisions used exact arithmetic. No new zero-free endpoint is claimed.")


if __name__ == "__main__":
    main()
