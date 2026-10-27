"""Numerical diagnostic only; pinned #84 Return/Formulas.lean, not a theorem."""
import numpy as np
from scipy.optimize import differential_evolution, minimize

THETA=.873985; H=.80545
PARENT=(.99,2.39)
PHYS=(49461297/50000000,23767/10000)
COUNT=(987987/1000000,2357/1000)

def count(delta,p,face,cap=.09999,capped=False,theta=THETA):
    B,L=face; kappa=2*theta-1; V=5/6-delta; z=cap-1e-7
    D=3-p if capped else 3-p-4*p/L
    A=2 if capped else 2-4*p/L
    C=1-2*p*z if capped else 1-2*p*B/L
    Z=1-C; U=(1-p)*C; J=V*D+delta*(1-p)*A
    N=(1-delta)*J+V*delta*U; T=J+delta*U
    RN=A*T+(Z-p)*J; DJ=D*J; MN=DJ+D*delta*U-RN
    naturalM=(1-4.5*.03)/2
    lower=.3800001 if capped else max(.3800001,(B-L*z)/2+1e-7)
    upper=min(.44-1e-7,naturalM-1e-7,(B-L*(z if capped else .03+1e-7))/2-1e-7)
    Dp=-1 if capped else -1-4/L; Ap=0 if capped else -4/L
    Cp=-2*z if capped else -2*B/L
    Up=-C+(1-p)*Cp; Jp=V*Dp+delta*(-A+(1-p)*Ap)
    guards=[D,A,C,J,T-J,1.2499*J-T,RN-23/37*DJ,DJ-RN,MN-lower*DJ,upper*DJ-MN,
      N-(1-2*delta*naturalM-2*delta*p*.03)*J,U*Jp-Up*J,.44-naturalM-1e-7,
      B-2*naturalM-L*(.03+1e-7)-2e-7,(z-.03-1e-7)*DJ if capped else np.ones_like(J)]
    guards=np.array(np.broadcast_arrays(*guards)); valid=np.all(guards>=0,axis=0)
    return N/J,valid,MN/DJ,np.min(guards,axis=0)

def old(delta,p,theta=THETA):
    k=2*theta-1; V=5/6-delta
    D=3-p-2*p/(3*k); C=2*(1-p)*(1-p/(3*k)); J=V*D+delta*C
    return 1-delta+delta*C*V/(2*J)

def capacities(theta,h,physical):
    ell=4*(1-theta)-1/3; y=h-2*ell; k=2*theta-1
    B,L=physical
    return [(d,min(d,2*y-d)/(6*k)) for d in [.005,.76]]+[(d,min(.06*d,(2*y-(2-B)*d)/L)) for d in [.76,h+1e-10]]

def result(delta,p,theta=THETA,h=H,physical=PARENT,counts=(PARENT,),detail=False):
    best=old(delta,p,theta); name='old'; width=np.nan
    for f in counts:
      for cap,capped in [(.09999,False),(.062,True)]:
        r,valid,m,guard=count(delta,p,f,cap,capped,theta)
        # Admission is required through p=1/2. Dense sampling is diagnostic only.
        _,vs,_,_=count(delta,np.linspace(p,.5,101),f,cap,capped,theta)
        if valid and np.all(vs) and r<best:
          best=r; name=(f,'cap' if capped else 'C'); width=cap-1e-7 if capped else (f[0]-2*m)/f[1]
    ell=4*(1-theta)-1/3; y=h-2*ell
    rows=[]
    for d,C in capacities(theta,h,physical):
      E=.5+13*h/75-y/2-ell/2-.09*d+delta/2+delta*p*(ell-C/2)+.75*d*best
      rows.append(E)
    val=max(rows)
    return (val,name,width,rows) if detail else val

if __name__=='__main__':
  for label,phys,counts in [('baseline',PARENT,(PARENT,)),('physical',PHYS,(PARENT,)),('both',PHYS,(PARENT,PHYS,COUNT))]:
    r=differential_evolution(lambda z:-result(*z,physical=phys,counts=counts),[(0,.75),(0,.5)],seed=7,popsize=12,tol=1e-11,maxiter=200)
    print(label,r.x,result(*r.x,physical=phys,counts=counts,detail=True),flush=True)
    print('capacities',capacities(THETA,H,phys),flush=True)
