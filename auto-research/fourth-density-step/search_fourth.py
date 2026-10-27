"""Floating-point scouting only; exact certification is a separate step."""
import json
import numpy as np
from scipy.optimize import minimize

B0,L0,c0=.99,2.39,.1
ts=np.linspace(0,1,81)
names=['q_lower','q_upper','q_floor','H_lower','retained_cap','retained_width','low_per_width','high_at_q','high_deriv','principal','second_ref','second_diag','ref_upper','selection_derivative']

def gates(z):
    s,dl,A,D=z
    B,L=B0-s*dl,L0-dl
    v=(.1-s)*ts
    w=s+v
    X=1+D*v
    u=A*v/X
    E=dl*X+(6*B0-L0)*A
    q=.999*L0*A/E
    H=1-6*u
    rho=1-10*q/(15-6*q)
    return np.array([q-.5,.75-q,q-.65,H-.9,c0*H-w+u,w-u,.001*L0*A/X,
      1-rho-q*B+q*(L-1)*w-(6*(1-rho)-q-1)*u,
      25/24*H-(B-(L-1)*w-u),1-B+(L-2)*w-4.5*u,
      .05+1.5*(1-B)+(1.5*L-2.5)*w-4.5*u,
      1-B+(L-1)*w-4*u,1/3-2*w-3*u,A/X**2])

def run(target):
    best=None
    for initial in [[.07,.025,.4,15],[.075,.03,.5,20],[.08,.02,.5,10],[.06,.01,.6,5],[.09,.01,1,20]]:
        r=minimize(lambda z:-z[1]*(target-z[0]),initial,method='SLSQP',
                   bounds=[(.0001,.0999),(.00001,.3),(.0001,10),(0,500)],
                   constraints={'type':'ineq','fun':lambda z:(gates(z)-1e-7).ravel()},
                   options={'maxiter':300,'ftol':1e-12})
        if r.success and np.min(gates(r.x))>0 and (best is None or r.fun<best.fun):best=r
    if best is None: return {'target':target,'found':False}
    s,dl,A,D=best.x
    g=gates(best.x)
    ans={'target':target,'parameters':best.x.tolist(),'B':B0-s*dl,'L':L0-dl,'gain':-best.fun,
         'minima':dict(zip(names,g.min(axis=1).tolist()))}
    print(json.dumps(ans,indent=2),flush=True)
    return ans

if __name__=='__main__':
    from pathlib import Path
    rows=[run(w) for w in [.06,.07,.08,.09,.1]]
    with Path(__file__).resolve().with_name('numerical-candidates.json').open('w') as f:json.dump(rows,f,indent=2)
