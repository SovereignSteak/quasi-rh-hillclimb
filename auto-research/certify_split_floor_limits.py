"""Exact sharp limits after separating floor and nonfloor intermediate counts.

Run: python auto-research/certify_split_floor_limits.py [--json PATH]
The k=2/3 nonfloor count is source-backed; adaptive R=1-delta remains an
idealization. Slopes k>2/3 are hypothetical analytic inputs, not proved here.
No new zero-free endpoint or Lean theorem is claimed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
from itertools import product
import sympy as s
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import certify as C

Q=s.Rational
L,H,D,K,U,T=s.symbols('ell h D k u t')
DR=(Q(71,96),Q(5,6))
KR=(Q(2,3),Q(1))
FLOOR=Q(167,192)
FLOOR_POINT={L:Q(3,16),H:Q(25,32)}
PAPER={L:Q(1,6),H:Q(13,16)}

def ident(expr):
    assert s.cancel(s.expand(expr))==0,expr

def positive(poly,intervals):
    variables=tuple(intervals)
    p=s.Poly(s.expand(poly),*variables)
    assert not p.as_expr().has(s.Float)
    assert all(p.degree(v)<=1 for v in variables)
    vals=[p.as_expr().subs(dict(zip(variables,point))) for point in product(*intervals.values())]
    assert all(v.is_Rational and v>0 for v in vals),vals
    return min(vals)

def positive_rational(expr,intervals):
    n,d=s.fraction(s.cancel(expr))
    positive(d,intervals)
    return positive(n,intervals)

def intermediate(delta):
    return -C.high_exponent(L,H,delta,delta/2,1-K*delta,Q(1,2))

def check_all():
    A=61-117*L-50*H
    B=s.expand(300*intermediate(D))
    original_intermediate=-C.high_exponent(L,H,D,D/2,Q(76,75)-2*D/3,Q(1,2))
    ident(intermediate(D).subs(K,Q(2,3))-original_intermediate-Q(1,150))
    weighted=s.expand((98+150*D)*A+50*B)
    ident(weighted-6*(1250*D*K-6675*D*L-350*D-3786*L+1213))
    ident(A+25*(2*H-1-3*L)-(36-192*L))
    LS=(1250*D*K-350*D+1213)/(3*(2225*D+1262))
    HS=(5975*D-1950*D*K+1187)/(2*(2225*D+1262))
    S=((24825-1250*K)*D+12669)/(12*(2225*D+1262))
    KC=(1025*D-322)/(800*D)
    ident(weighted.subs(L,LS))
    ident(A.subs({L:LS,H:HS}))
    ident(B.subs({L:LS,H:HS}))
    ident(S-(Q(11,12)-LS/4))
    ident(S.subs({D:Q(5,6),K:Q(2,3)})-Q(587917,673092))
    ident(S.subs({D:Q(3,4),K:Q(2,3)})-Q(122651,140676))
    ident(LS.subs(K,KC)-Q(3,16))
    ident(HS.subs(K,KC)-Q(25,32))
    positive_rational(KC-Q(2,3),{D:DR})
    positive_rational(1-KC,{D:DR})
    positive_rational(LS.subs(K,Q(2,3))-Q(1,6),{D:DR})
    positive_rational(HS.subs(K,Q(2,3))-Q(1,2),{D:DR})
    assert FLOOR_POINT[H] > Q(1,2) and PAPER[H] > Q(1,2)
    print('PASS fixed-D necessary frontier max(167/192, S_k(D)), transition kcrit(D)')

    baseline={L:LS.subs(K,Q(2,3)),H:HS.subs(K,Q(2,3)),K:Q(2,3)}
    transition={**FLOOR_POINT,K:KC}
    segment={v:(1-T)*baseline[v]+T*transition[v] for v in (L,H,K)}
    ident(LS.subs(K,segment[K])-segment[L])
    ident(HS.subs(K,segment[K])-segment[H])
    sides=C.side_constraints(L,H)
    fk='floor bin (delta0=1/50, R=1, q=delta0/2): -E(h)'
    ik='intermediate d=1/2, delta=5/6'
    lk='intermediate d=1/2, delta=1/50'
    sides[ik]=intermediate(D)
    sides[lk]=intermediate(Q(1,50))
    assert len(sides)==12
    ident(150*sides[fk]-A)
    ident(sides['b > 0']-(2*H-1-3*L))
    for name,expr in sides.items():
        if name.startswith('prime supply'):
            expr=s.cancel(H*expr)
        assert s.Poly(expr,L,H,K).total_degree()<=1
        b=expr.subs(baseline)
        t=expr.subs(transition)
        if name in (fk,ik):
            ident(b);ident(t)
        elif name=='b > 0':
            positive_rational(b,{D:DR});ident(t)
        else:
            positive_rational(b,{D:DR})
            positive_rational(t,{D:DR})
        ident(expr.subs(segment)-(1-T)*b-T*t)
        positive_rational(expr.subs(PAPER),{D:DR,K:KR})

    ideal=-C.high_exponent(L,H,C.d,(Q(1,2)-C.y)*C.d,1-C.d,H)
    rectangle={C.d:(Q(0),Q(5,6)),C.y:(Q(0),Q(1,2))}
    positive_rational(ideal.subs(baseline),{D:DR,**rectangle})
    positive(ideal.subs(FLOOR_POINT),rectangle)
    positive(ideal.subs(PAPER),rectangle)
    positive(Q(33,50)+(Q(1,2)-K)*C.d,
             {K:KR,C.d:(Q(1,50),Q(5,6))})
    positive(Q(33,50)-C.d/2,rectangle)
    assert 1+Q(1,100)-Q(17,50)>0
    ident(ideal.subs(segment)-(1-T)*ideal.subs(baseline)-T*ideal.subs(transition))
    ident(intermediate(D).subs(FLOOR_POINT)-D*(K-KC)/2)
    ident(s.diff(intermediate(Q(1,50)),K)-Q(1,100))
    print('PASS global sharpness: all remaining sides and full ideal rectangle; two phases')

    F=s.factor(S.subs(D,2*U-1))
    P=26700*U**2+(1250*K-30603)*U+6078-625*K
    ident(U-F-P/(6*(4450*U-963)))
    ident(weighted.subs({D:2*U-1,L:Q(11,3)-4*U})-12*P)
    KSTAR=Q(41863,56800)
    ident(KC.subs(D,2*FLOOR-1)-KSTAR)
    ident(P.subs(U,FLOOR)-(1250*FLOOR-625)*(K-KSTAR))
    positive(s.diff(P,U),{U:(FLOOR,Q(7,8)),K:KR})
    positive(P.subs(U,Q(7,8)),{K:KR})
    derivative=625*(5025-2524*K)/(6*(4450*U-963)**2)
    ident(s.diff(F,U)-derivative)
    positive(5025-2524*K,{K:KR})
    positive(4450*U-963,{U:(FLOOR,Q(7,8))})
    assert derivative.subs({K:Q(2,3),U:FLOOR})<Q(1,20)
    discriminant=1562500*K**2-9757500*K+287413209
    positive(-s.diff(discriminant,K),{K:KR})
    assert discriminant.subs(K,1)>0
    root=(30603-1250*K+s.sqrt(discriminant))/53400
    ident(P.subs(U,root))
    ident(root.subs(K,Q(2,3))-(89309+s.sqrt(2534423881))/160200)
    ident(root.subs(K,KSTAR)-FLOOR)
    baseline_polynomial=80100*U**2-89309*U+16984
    ident(3*P.subs(K,Q(2,3))-baseline_polynomial)
    root_lo=Q(8717357171994976,10**16)
    root_hi=Q(8717357171994977,10**16)
    assert baseline_polynomial.subs(U,root_lo)<0<baseline_polynomial.subs(U,root_hi)
    assert FLOOR<root_lo<root_hi<Q(7,8)
    assert 0<2534423881<2542433881  # Exact improvement over PR #29's larger radical.
    assert Q(2,3)<KSTAR<1
    target_slope=Q(16869,23125)
    target=Q(87,100)
    ident(P.subs(U,target)-(1250*target-625)*(K-target_slope))
    assert Q(2,3)<target_slope<KSTAR
    print('PASS bootstrap polynomial, unique fixed point, threshold 41863/56800')
    print('PASS target sigma=87/100 requires slope k>16869/23125 in this ideal budget')
    print('Derivative satisfies 0 < f_k prime < 1/20 on full u and k rectangle')

    runs=[]
    for kval in (Q(2,3),Q(7,10),KSTAR,Q(3,4),Q(1)):
        current=Q(7,8)
        witnesses=[]
        for n in range(10):
            cap=2*current-1
            edge=max(FLOOR,F.subs({U:current,K:kval}))
            nxt=Q(s.ceiling(edge*10**(6+n))+1,10**(6+n))
            assert edge<nxt<current
            limiting={L:LS.subs({D:cap,K:kval}),H:HS.subs({D:cap,K:kval})}
            if kval>=KC.subs(D,cap):
                limiting=FLOOR_POINT
            ell=Q(11,3)-4*nxt
            t=s.cancel((limiting[L]-ell)/(limiting[L]-Q(1,6)))
            assert 0<t<1
            height=s.cancel(t*Q(13,16)+(1-t)*limiting[H])
            point={L:ell,H:height,D:cap,K:kval}
            margins={name:s.cancel(value.subs(point)) for name,value in sides.items()}
            assert all(v.is_Rational and v>0 for v in margins.values())
            ideal_bound=positive(ideal.subs(point),rectangle)
            witnesses.append({"step":n+1,"incoming_boundary":str(current),
                              "incoming_delta_cap":str(cap),"strict_frontier":str(edge),
                              "sigma":str(nxt),"ell":str(ell),"h":str(height),
                              "interpolation_weight":str(t),
                              "least_side_margin":str(min(margins.values())),
                              "ideal_adaptive_lower_bound":str(ideal_bound)})
            current=nxt
        runs.append({"slope":str(kval),
                     "sharp_infimum":str(root.subs(K,kval) if kval<KSTAR else FLOOR),
                     "witnesses":witnesses,
                     "final_side_margins":{name:str(value) for name,value in margins.items()}})
        print(f'PASS ten strict incoming-ceiling steps, k={kval}, final sigma={current}')

    bad_sigma=Q(87173,100000)
    bad_weighted=s.cancel(12*P.subs({U:bad_sigma,K:Q(2,3)}))
    assert bad_weighted<0
    assert Q(86979,100000)<FLOOR
    last=runs[0]["witnesses"][-1]
    actual,denominator=C.adaptive_poly(Q(last["ell"]),Q(last["h"]))
    location={C.d:Q(2,5),C.y:Q(0)}
    actual_value=actual.as_expr().subs(location)
    assert actual_value<0<denominator.as_expr().subs(location)
    print('PASS exact negative controls below split-floor and floor/b limits')
    print('PASS original adaptive count rejects the final ideal k=2/3 witness')
    print('All exact checks passed. k>2/3 remains a hypothetical analytic input.')
    return {"schema":"quasi-rh-split-floor-density-phase-v1",
            "status":"proved finite-budget statement",
            "scope":"Adaptive R=1-delta is hypothetical; k>2/3 intermediate estimates are hypothetical; no new zero-free endpoint",
            "nonfloor_count":"1-k*delta","floor_count":"1",
            "delta_interval":[str(v) for v in DR],"slope_interval":[str(v) for v in KR],
            "fixed_ceiling_frontier":"max(167/192, ((24825-1250*k)*D+12669)/(12*(2225*D+1262)))",
            "fixed_ceiling_transition":str(KC),"bootstrap_transition":str(KSTAR),
            "target_boundary":str(target),"strict_slope_threshold_for_target":str(target_slope),
            "bootstrap_polynomial":str(P),"bootstrap_larger_root":str(root),
            "source_slope_infimum":"(89309+sqrt(2534423881))/160200",
            "source_slope_root_enclosure":[str(root_lo),str(root_hi)],
            "saturated_infimum":str(FLOOR),"runs":runs,
            "negative_controls":{"source_slope_sigma":str(bad_sigma),
                                 "positive_combination_at_infeasible_sigma":str(bad_weighted),
                                 "actual_adaptive_F_at_final_ideal_witness":str(actual_value)},
            "source_sha256":{"certify.py":hashlib.sha256(Path(C.__file__).read_bytes()).hexdigest(),
                             Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
            "environment":{"python":sys.version.split()[0],"sympy":s.__version__}}


def main():
    if not __debug__:
        raise SystemExit("Exact checks require assertions; run Python without -O.")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path,help="write the checked formulas and rational witnesses")
    args=parser.parse_args()
    receipt=check_all()
    if args.json:
        args.json.write_text(json.dumps(receipt,indent=2)+"\n")
    print("Displayed approximation only:",s.N((89309+s.sqrt(2534423881))/160200,26))


if __name__=='__main__':
    main()
