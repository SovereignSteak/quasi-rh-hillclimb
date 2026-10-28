"""Independent read-only audit of the proposed fourth-transition receipt.
All basis coefficients reconstructed by a linear solve against the Bernstein basis.
"""
from pathlib import Path
import json,sys
import sympy as S
Q=S.Rational
v,t=S.symbols('v t')
if not __debug__: raise SystemExit('Assertions required; do not use -O.')
receipt_path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('exact-fourth-receipts.json')
receipt=json.loads(receipt_path.read_text())
assert receipt['source_head']=='71996e7e79840455f7beead063a73b7b31cfb586'
rows=receipt['cases']
assert [row['name'] for row in rows]==['known_third','fourth_physical','fourth_count']

def independent_basis(poly,lo,hi):
    p=S.Poly(poly.subs(v,lo+(hi-lo)*t),t)
    n=max(p.degree(),0)
    bases=[S.Poly(S.binomial(n,k)*t**k*(1-t)**(n-k),t) for k in range(n+1)]
    matrix=S.Matrix([[b.nth(j) for b in bases] for j in range(n+1)])
    coefs=list(matrix.inv()*S.Matrix([p.nth(j) for j in range(n+1)]))
    assert S.expand(sum(c*b.as_expr() for c,b in zip(coefs,bases))-p.as_expr())==0
    return coefs

expected_parameters={
 'known_third': ('4967/5000','49/20','1/10','99/100','239/100','1/10','3/5','35'),
 'fourth_physical': ('99/100','239/100','1/10','49461297/50000000','23767/10000','1/10','27/50','94'),
 'fourth_count': ('99/100','239/100','1/10','987987/1000000','2357/1000','1/10','103/200','23'),
}
for row in rows:
    B0,L0,c0,B,L,c,A,D=[Q(row['parameters'][key]) for key in ['B0','L0','c0','B','L','c','A','D']]
    assert (B0,L0,c0,B,L,c,A,D)==tuple(map(Q,expected_parameters[row['name']]))
    s=(B0-B)/(L0-L); hi=c-s; w=s+v
    assert B<=B0<1 and 1<L<L0 and 0<c<Q(1,6) and 0<c0<Q(1,6)
    assert 0<=s<c and Q(row['crossing'])==s and Q(row['upper_excess'])==hi
    X=1+D*v; E=(L0-L)*X+(6*B0-L0)*A; K=Q(999,1000)*L0*A
    u=A*v/X; q=K/E; H=1-6*u
    J=10*q*H/(15-6*q)-q*(B-(L-1)*w-u)+u
    functions={
      'selection_denominator':X,'density_denominator':E,'high_denominator':15*E-6*K,
      'q_lower':q-Q(1,2),'q_upper':Q(3,4)-q,'q_floor':q-Q(13,20),
      'H_lower':H-Q(9,10),'retained_cap':c0*H-w+u,'retained_width':w-u,
      'low_per_width':L0*A/(1000*X),'high_at_q':J,
      'high_deriv':Q(25,24)*H-B+(L-1)*w+u,
      'principal':1-B+(L-2)*w-Q(9,2)*u,
      'second_ref':Q(1,20)+Q(3,2)*(1-B)+(Q(3,2)*L-Q(5,2))*w-Q(9,2)*u,
      'second_diag':1-B+(L-1)*w-4*u,'ref_upper':Q(1,3)-2*w-3*u,
      'selection_derivative':S.diff(u,v),
    }
    low=L0*u-q*((L0-L)*v+(6*B0-L0)*u)
    assert S.cancel(low-L0*u/1000)==0
    assert S.cancel(low/v-functions['low_per_width'])==0
    assert S.cancel(S.diff(u,v)-A/X**2)==0
    assert functions.keys()==row['gates'].keys()
    nboxes=0
    for name,f in functions.items():
        gate=row['gates'][name]
        num=S.sympify(gate['numerator'],locals={'v':v}); den=S.sympify(gate['denominator'],locals={'v':v})
        assert not (num.has(S.Float) or den.has(S.Float))
        assert S.cancel(num/den-f)==0,(row['name'],name)
        boxes=sorted(gate['boxes'],key=lambda b:Q(b['lo']))
        assert Q(boxes[0]['lo'])==0 and Q(boxes[-1]['hi'])==hi
        reserves=[]
        for i,box in enumerate(boxes):
            lo,up=Q(box['lo']),Q(box['hi'])
            assert 0<=lo<up<=hi
            if i: assert Q(boxes[i-1]['hi'])==lo
            nb=independent_basis(num,lo,up); db=independent_basis(den,lo,up)
            assert min(nb)>0 and min(db)>0
            assert Q(box['numerator_lower'])==min(nb)
            assert Q(box['denominator_lower'])==min(db)
            assert Q(box['denominator_upper'])==max(db)
            bound=min(nb)/max(db)
            assert Q(box['gate_lower'])==bound
            reserves.append(bound)
        assert Q(gate['uniform_lower'])==min(reserves)>0
        nboxes+=len(boxes)
    print(row['name'],': 17 exact functions and',nboxes,'covering Bernstein boxes independently checked')
    print('  cross',s,'upper_excess',hi,'high_at_q reserve',row['gates']['high_at_q']['uniform_lower'])
    for width in [Q(3,50),Q(7,100),Q(1,10)]:
        gain=(B-L*width)-(B0-L0*width)
        assert gain==(L0-L)*(width-s)
        print('  boundary gain at',width,':',gain)

print('Exact source scalar receipt replay PASS; no analytic or Lean instantiation claimed.')
