"""Independent exact replay of fourth-transition return scalar receipt."""
from pathlib import Path
import json,sys
import sympy as S
Q=S.Rational
v,p,x,t=S.symbols('delta p x t')
if not __debug__: raise SystemExit('Assertions required; do not use -O.')
receipt_path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('exact-return-receipt.json')
R=json.loads(receipt_path.read_text())
assert R['source_head']=='71996e7e79840455f7beead063a73b7b31cfb586'
theta=Q(R['theta']);h=Q(R['h']);reserve=Q(R['reserve'])
assert Q(873,1000)<theta<Q(7,8) and Q(793,1000)<h<Q(806,1000) and reserve==Q(1,10**8)
B0,L0=Q(99,100),Q(239,100);BP,LP=map(Q,R['physical_face']);BC,LC=map(Q,R['count_face'])
assert (BP,LP)==(Q(49461297,50000000),Q(23767,10000))
assert (BC,LC)==(Q(987987,1000000),Q(2357,1000))
eps=Q(1,10**7);naturalM=Q(173,400);kap=2*theta-1;ell=4*(1-theta)-Q(1,3);y=h-2*ell
# Literal windows independently extracted from pinned Return/Windows.lean.
# Source head: 71996e7e79840455f7beead063a73b7b31cfb586
# UTF-8 source SHA256: 07ae20faff8f31fcc6c21415573fb60e3aacf559d128ad8054adc028560d3c28
WINDOW_DATA = [(1, 'capP', '9/32', '3/8', '3/8'), (2, 'capP', '9/32', '21/64', '7/16'), (3, 'C', '43/128', '3/8', '7/16'), (4, 'C', '3/8', '15/32', '3/8'), (5, 'C', '3/8', '27/64', '7/16'), (6, 'C', '27/64', '15/32', '7/16'), (7, 'C', '27/64', '57/128', '15/32'), (8, 'C', '27/64', '111/256', '31/64'), (9, 'C', '111/256', '57/128', '31/64'), (10, 'C', '111/256', '225/512', '63/128'), (11, 'C', '225/512', '57/128', '63/128'), (12, 'C', '225/512', '453/1024', '127/256'), (13, 'C', '453/1024', '57/128', '127/256'), (14, 'C', '57/128', '15/32', '15/32'), (15, 'C', '15/32', '33/64', '7/16'), (16, 'capP', '33/64', '69/128', '15/32')]
wins={i:(kind,Q(lo),Q(hi),Q(pl)) for i,kind,lo,hi,pl in WINDOW_DATA}
assert len(wins)==16
# Definitions copied from Lean Formulas, not the candidate certifier.
def bf(B=None,L=None,cap=False):
    V=Q(5,6)-v
    if B is None:
        D=3-p-2*p/(3*kap);C=2*(1-p)*(1-p/(3*kap));J=V*D+v*C
        return J,(1-v)*J+v*C*V/2,[J]
    z=(Q(31,500) if cap else Q(9999,100000))-eps
    D=3-p if cap else 3-p-4*p/L
    A=Q(2) if cap else 2-4*p/L
    C0=1-2*p*z if cap else 1-2*p*B/L
    Z=1-C0;U=(1-p)*C0;J=V*D+v*(1-p)*A;N=(1-v)*J+V*v*U;T=J+v*U
    RN=A*T+(Z-p)*J;DJ=D*J;MN=D*T-RN
    lower=Q(19,50)+eps if cap else max(Q(19,50)+eps,(B-L*z)/2+eps)
    upper=min(Q(11,25)-eps,naturalM-eps,(B-L*(z if cap else Q(3,100)+eps))/2-eps)
    Dp=-1 if cap else -1-4/L;Ap=0 if cap else -4/L;Cp=-2*z if cap else -2*B/L
    Up=-C0+(1-p)*Cp;Jp=V*Dp+v*(-A+(1-p)*Ap)
    gs=[D,A,C0,J,T-J,Q(12499,10000)*J-T,RN-Q(23,37)*DJ,DJ-RN,
        MN-lower*DJ,upper*DJ-MN,N-(1-2*v*naturalM-2*v*p*Q(3,100))*J,
        U*Jp-Up*J,Q(11,25)-naturalM-eps,B-2*naturalM-L*(Q(3,100)+eps)-2*eps,
        (z-Q(3,100)-eps)*DJ if cap else Q(1)]
    return J,N,gs
branches={'old':bf(),'parentC':bf(B0,L0),'parentCap':bf(B0,L0,True),'fourthC':bf(BC,LC)}

basis_inv={}
def invbasis(n):
    if n not in basis_inv:
        pols=[S.Poly(S.binomial(n,i)*x**i*(1-x)**(n-i),x) for i in range(n+1)]
        basis_inv[n]=S.Matrix([[b.nth(j) for b in pols] for j in range(n+1)]).inv()
    return basis_inv[n]

def independent_coeffs(expr,box):
    a,b,c,d=box
    pol=S.Poly(S.expand(expr).subs({v:a+(b-a)*x,p:c+(d-c)*t}),x,t)
    n,m=max(pol.degree(x),0),max(pol.degree(t),0)
    power=S.Matrix([[pol.coeff_monomial(x**i*t**j) for j in range(m+1)] for i in range(n+1)])
    coefs=invbasis(n)*power*invbasis(m).T
    return list(coefs)

def check_cover(boxes,target):
    a,b,c,d=target
    assert boxes and a<b and c<d
    for lo,hi,pl,pu in boxes:assert a<=lo<hi<=b and c<=pl<pu<=d
    cuts=sorted({a,b,*(z for box in boxes for z in box[:2])})
    for lo,hi in zip(cuts,cuts[1:]):
        intervals=sorted((pl,pu) for dl,du,pl,pu in boxes if dl<=lo and hi<=du)
        assert intervals and intervals[0][0]==c and intervals[-1][1]==d
        for first,second in zip(intervals,intervals[1:]):assert first[1]==second[0]

expected={(i,name) for i,(kind,lo,hi,pl) in wins.items()
          for name in (['parentCap'] if kind=='capP' else ['parentC','fourthC'])}
seen=set();admissionboxes=0
for adm in R['admission']:
    key=(adm['window'],adm['branch']);assert key in expected and key not in seen;seen.add(key)
    kind,lo,hi,pl=wins[key[0]];boxes=[]
    assert 0<=lo<hi<=Q(3,4) and 0<=pl<=Q(1,2)
    for cell in adm['cells']:
        box=tuple(map(Q,cell['box']));boxes.append(box)
        lbs=[min(independent_coeffs(g,box)) for g in branches[key[1]][2]]
        assert len(lbs)==15 and all(a>0 for a in lbs)
        assert lbs==list(map(Q,cell['lower']))
    check_cover(boxes,(lo,hi,pl,Q(1,2)));admissionboxes+=len(boxes)
assert seen==expected
print('PASS 29 entire upward admission windows,',admissionboxes,'boxes; all15 guards independently reconstructed')

# Old denominator positivity over the entire return domain is a separate obligation.
oldlb=min(independent_coeffs(branches['old'][0],(0,Q(3,4),0,Q(1,2))))
assert oldlb>0
print('PASS global old denominator Bernstein lower:',oldlb)

ds=[Q(1,200),Q(19,25),Q(19,25),h+Q(1,10**10)]
Cs=[min(d,2*y-d)/(6*kap) if i<2 else min(Q(3,50)*d,(2*y-(2-BP)*d)/LP) for i,d in enumerate(ds)]
assert Cs==list(map(Q,R['capacities']))
margin={}
for name,(J,N,_) in branches.items():
    for edge,(d,C) in enumerate(zip(ds,Cs)):
        E=Q(1,2)+Q(13,75)*h-y/2-ell/2-Q(9,100)*d+v/2+v*p*(ell-C/2)
        margin[name,edge]=S.expand(J*(theta-reserve-E)-Q(3,4)*d*N)
boxes=[];counts={name:0 for name in branches};globalmin=None
for cell in R['return']:
    box=tuple(map(Q,cell['box']));boxes.append(box)
    assert {r['edge'] for r in cell['edges']}==set(range(4)) and len(cell['edges'])==4
    for row in cell['edges']:
        name=row['branch'];edge=row['edge'];assert name in branches
        if name!='old':
            assert any(n==name and wins[i][1]<=box[0] and box[1]<=wins[i][2] and wins[i][3]<=box[2]
                       for i,n in seen)
        lbs=independent_coeffs(margin[name,edge],box);lb=min(lbs)
        assert lb==Q(row['margin_lower']) and lb>0
        counts[name]+=1
        globalmin=lb if globalmin is None else min(globalmin,lb)
check_cover(boxes,(0,Q(3,4),0,Q(1,2)))
print('PASS entire return rectangle covered exactly by',len(boxes),'closed boxes with four edge certificates each')
print('Selected branch counts:',counts,'smallest cleared margin',globalmin)
print('PASS capacities recomputed:',Cs)
# PhysicalSchedule requirements; incumbent is naturalK/6, not naturalK.
assert 0<=Q(3,50)<Q(1,5) and Q(3,4)<ds[1]<=ds[3] and y<ds[1]<2*y
assert 2<=LP<=Q(9,2) and 0<BP<=1
assert 1-BP/2-(Q(9,2)-LP/2)*Q(3,50)>=0 and ell/ds[3]>Q(1,5)
assert kap<=Q(3,4)
assert reserve>Q(1,10**9)
print('PASS PhysicalSchedule finite geometry; corrected incumbent reserve',Q(3,4)-kap)
print('PASS certificate reserve1e-8 exceeds inherited rowFee1e-9')

# Entire Geometry.Parameters and BoundsN contracts, including the floor row.
xx=1+ell-h;signal=theta-(4+y-xx)/6
identities={'x_plus_y':xx+y-(1-ell),'signal_boundary':signal-(xx/2+(y-xx)/12)}
assert all(z==0 for z in identities.values())
assert R['identities']=={k:str(z) for k,z in identities.items()}
geom={
 'theta_lower':theta-Q(873,1000),'theta_upper':Q(7,8)-theta,
 'h_lower':h-Q(793,1000),'h_upper':Q(806,1000)-h,
 'y_lower':y-Q(458,1000),'y_upper':Q(467,1000)-y,
 'ell_lower':ell-Q(1672,10000),'ell_upper':Q(171,1000)-ell,
 'small_saving':y/2-h*(Q(17,50)-Q(1,6))-Q(1,50)-Q(7,100),
 'floor_margin':signal-Q(1,200)-(Q(4,25)*xx-Q(3,20)-Q(51,100)*y+Q(67,100)*ds[3]-Q(3,20)*ell),
 'ell_positive':ell,'ell_sixth':ell-Q(1,6),'ell_fifth':Q(1,5)-ell,
 'ell_lt_x':xx-ell,'x_lt_y':y-xx,'y_half':Q(1,2)-y,
 'dilation_gap':2*xx-y-ell,'tuple_margin_neg':2*(xx+y)-1-3*ell,
 'cap_positive':Q(3,50),'cap_lt_fifth':Q(1,5)-Q(3,50),
 'physical_source_cap':Q(1,10)-Q(3,50),
 'physical_marked_vs_declared_cap':Q(31,500)-Q(3,50),
 'physical_declared_vs_source_cap':Q(1,10)-Q(31,500),
 'count_source_cap':Q(1,10)-Q(9999,100000),
 'inherited_cap_source_cap':Q(1,10)-Q(31,500),
 'old_start_positive':ds[0],'old_interval_width':ds[1]-ds[0],
 'switch_lower':ds[1]-Q(3,4),'switch_top':ds[3]-ds[1],
 'y_switch':ds[1]-y,'switch_twoy':2*y-ds[1],
 'lambda_lower':LP-2,'lambda_upper':Q(9,2)-LP,'B_lower':BP,'B_upper':1-BP,
 'small_plain':1-BP/2-(Q(9,2)-LP/2)*Q(3,50),'prime_supply':ell/ds[3]-Q(1,5),
 'incumbent':Q(3,4)-kap,'physical_crossing_overlap':Cs[3]/ds[3]-Q(291,5000),
 'kappa_positive':kap,**{f'capacity_{i}_positive':C for i,C in enumerate(Cs)},
 'reserve_vs_rowfee':reserve-Q(1,10**9)}
assert geom.keys()==R['geometry'].keys()
assert all(z>0 for z in geom.values()),{k:z for k,z in geom.items() if z<=0}
assert all(z==Q(R['geometry'][k]) for k,z in geom.items())
oldboxes=[]
for cell in R['old_denominator']:
    box=tuple(map(Q,cell['box']));oldboxes.append(box)
    lb=min(independent_coeffs(branches['old'][0],box))
    assert lb>0 and cell['lower']==[str(lb)]
check_cover(oldboxes,(0,Q(3,4),0,Q(1,2)))
print('PASS full Geometry.Parameters and BoundsN, all recorded finite fields:',len(geom))
print('PASS floor slack:',geom['floor_margin'],'at theta=',theta,'h=',h)
# Negative geometry control: this point passed the other row search but fails
# the actual floor condition. Recompute from the full Lean expression.
neg=R['negative_control'];nt,nh=Q(neg['theta']),Q(neg['h'])
assert nt==Q(436991,500000) and nh==Q(8059,10000)
ne=4*(1-nt)-Q(1,3);nx=1+ne-nh;ny=nh-2*ne;ndp=nh+Q(1,10**10)
ns=nt-(4+ny-nx)/6
nf=ns-Q(1,200)-(Q(4,25)*nx-Q(3,20)-Q(51,100)*ny+Q(67,100)*ndp-Q(3,20)*ne)
assert neg['failed_field']=='BoundsN.floor_margin'
assert nf==Q(neg['margin'])==Q(-428480201,3000000000000)<0
print('PASS negative geometry control rejects theta=.873982,h=.8059 with floor margin',nf)
print('Complete exact scalar receipt audit PASS; analytic/Lean assembly not independently built.')
