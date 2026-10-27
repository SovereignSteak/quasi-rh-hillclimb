"""Numerical theta/h search using fixed PR84 windows; no endpoint theorem."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, differential_evolution
from return_probe import *

WINDOWS=[('cap',9/32,3/8,3/8),('cap',9/32,21/64,7/16),('C',43/128,3/8,7/16),
 ('C',3/8,15/32,3/8),('C',3/8,27/64,7/16),('C',27/64,15/32,7/16),
 ('C',27/64,57/128,15/32),('C',27/64,111/256,31/64),('C',111/256,57/128,31/64),
 ('C',111/256,225/512,63/128),('C',225/512,57/128,63/128),('C',225/512,453/1024,127/256),
 ('C',453/1024,57/128,127/256),('C',57/128,15/32,15/32),('C',15/32,33/64,7/16),
 ('cap',33/64,69/128,15/32)]

def window_count(delta,p,theta,counts,include_old=True):
    best=old(delta,p,theta) if include_old else np.full_like(old(delta,p,theta),np.inf)
    for kind,lo,hi,pl in WINDOWS:
      faces=[PARENT] if kind=='cap' else counts
      for face in faces:
        r,_,_,_=count(delta,p,face,.062 if kind=='cap' else .09999,kind=='cap',theta)
        avail=(delta>=lo)&(delta<=hi)&(p>=pl)&(p<=.5)
        best=np.minimum(best,np.where(avail,r,np.inf))
    return best

def row(delta,p,theta,h,physical=PHYS,counts=(PARENT,COUNT),edge=3):
    rc=window_count(delta,p,theta,counts)
    ell=4*(1-theta)-1/3;y=h-2*ell;d,C=capacities(theta,h,physical)[edge]
    return .5+13*h/75-y/2-ell/2-.09*d+delta/2+delta*p*(ell-C/2)+.75*d*rc

def check_windows():
    mins=[]
    for i,(kind,lo,hi,pl) in enumerate(WINDOWS):
      faces=[PARENT] if kind=='cap' else [PARENT,COUNT]
      for face in faces:
        ds,ps=np.meshgrid(np.linspace(lo,hi,101),np.linspace(pl,.5,101),indexing='ij')
        _,_,_,g=count(ds,ps,face,.062 if kind=='cap' else .09999,kind=='cap')
        mins.append(dict(window=i+1,face=list(face),min_sampled_guard=float(np.min(g))))
    return mins

def exact_geometry_values(theta,h,physical=PHYS):
    ell=4*(1-theta)-1/3;x=1+ell-h;y=h-2*ell;dp=h+1e-10;B,L=physical
    signal=theta-(4+y-x)/6
    return dict(theta_min=theta-.873,theta_max=.875-theta,h_min=h-.793,h_max=.806-h,
      ell_min=ell-.1672,ell_max=.171-ell,y_min=y-.458,y_max=.467-y,
      small_saving=y/2-h*(17/50-1/6)-.02-.07,
      floor_margin=signal-.005-(.16*x-.15-.51*y+.67*dp-.15*ell),
      ell_pos=ell,ell_sixth=ell-1/6,ell_fifth=.2-ell,ell_x=x-ell,x_y=y-x,y_half=.5-y,
      dilation_gap=2*x-y-ell,tuple_margin=2*(x+y)-1-3*ell,
      switch_min=.76-.75,switch_top=dp-.76,y_switch=.76-y,switch_twoy=2*y-.76,
      lambda_min=L-2,lambda_max=4.5-L,B_min=B,B_max=1-B,
      small_plain=1-B/2-(4.5-L/2)*.06,prime_supply=ell/dp-.2,incumbent=.75-(2*theta-1))

def optimize_grid():
    # Include every fixed-window boundary and p=.5 exactly.
    ds=np.unique(np.r_[np.linspace(0,.75,1501),[z for w in WINDOWS for z in w[1:3]]])[:,None]
    ps=np.unique(np.r_[np.linspace(0,.5,1001),[w[3] for w in WINDOWS]])[None,:]
    # Count nonold branches are independent of theta, cached once.
    newer=window_count(ds,ps,THETA,(PARENT,COUNT),include_old=False)
    def worst(theta,h,full=False):
      rc=np.minimum(old(ds,ps,theta),newer)
      ell=4*(1-theta)-1/3;y=h-2*ell
      records=[]
      for edge,(d,C) in enumerate(capacities(theta,h,PHYS)):
        mat=.5+13*h/75-y/2-ell/2-.09*d+ds/2+ds*ps*(ell-C/2)+.75*d*rc
        ind=np.unravel_index(np.argmax(mat),mat.shape)
        records.append(dict(edge=edge,value=float(mat[ind]),delta=float(ds[ind[0],0]),p=float(ps[0,ind[1]])))
      return records if full else max(r['value'] for r in records)
    def obj(z):return z[0]
    def cons(z):
      theta,h=z
      return np.r_[theta-1e-8-worst(theta,h),list(exact_geometry_values(theta,h).values())]
    opt=minimize(obj,[.87398,.80545],method='SLSQP',bounds=[(.8739,.873985),(.804,.805999)],
      constraints=[{'type':'ineq','fun':cons}],options={'ftol':1e-13,'maxiter':50})
    theta,h=map(float,opt.x)
    return dict(success=bool(opt.success),message=opt.message,theta=theta,h=h,
      grid_margin=float(cons(opt.x)[0]),worst_edges=worst(theta,h,True),geometry=exact_geometry_values(theta,h)),worst

if __name__=='__main__':
    guards=check_windows()
    print('sampled admission minimum',min(g['min_sampled_guard'] for g in guards),flush=True)
    opt,worst=optimize_grid()
    print(json.dumps(opt,indent=2),flush=True)
    checks=[]
    for theta,h in [(THETA,H),(.873981,.80545),(.873981,.80546),(.8739808,.8054602)]:
      rr=worst(theta,h,True); checks.append(dict(theta=theta,h=h,edges=rr,margin=theta-1e-8-max(r['value'] for r in rr)))
    report=dict(status='NUMERICAL ONLY: grid search, not proof; exact-return-receipt.json certifies the conservative rational point separately',windows=WINDOWS,admission_samples=guards,optimum=opt,rational_trials=checks)
    with Path(__file__).resolve().with_name('return-search.json').open('w') as f:json.dump(report,f,indent=2);f.write('\n')
    print(json.dumps(checks,indent=2))
