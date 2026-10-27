"""Exact parent-only scalar ablation at the final proposed theta and h."""
import json
from pathlib import Path
import sympy as s
from return_certify import THETA,H,Q,PARENT,PHYS,COUNT,branch,delta,p

def main():
    if not __debug__:raise SystemExit('Assertions required; do not use -O')
    at={delta:Q(11,25),p:Q(1,2)}
    ell=4*(1-THETA)-Q(1,3);y=H-2*ell;d=H+Q(1,10**10)
    records=[]
    for name,physical,faces in [('parent_only',PARENT,[None,PARENT]),
      ('new_physical_only',PHYS,[None,PARENT]),
      ('new_count_only',PARENT,[None,PARENT,COUNT]),
      ('both_fourth_faces',PHYS,[None,PARENT,COUNT])]:
      values=[s.cancel(N.subs(at)/J.subs(at)) for J,N,_ in map(branch,faces)]
      best=min(values);B,L=physical
      C=min(Q(3,50)*d,(2*y-(2-B)*d)/L)
      E=Q(1,2)+Q(13,75)*H-y/2-ell/2-Q(9,100)*d+Q(11,50)+Q(11,50)*(ell-C/2)+Q(3,4)*d*best
      excess=s.cancel(E-THETA)
      records.append({'case':name,'counts':list(map(str,values)),'minimum_count':str(best),
        'capacity':str(C),'exponent':str(E),'excess_over_theta':str(excess)})
    assert Q(records[0]['excess_over_theta'])>0
    assert Q(records[1]['excess_over_theta'])>0
    assert Q(records[3]['excess_over_theta'])<0
    report={'status':'Exact point diagnostic, not a global optimum or analytic endpoint theorem',
      'theta':str(THETA),'h':str(H),'delta':'11/25','p':'1/2','edge':'newTop',
      'available_parent_branches':['old','parentC'],
      'unavailable_parent_branch':'parentCap (delta outside every inherited capP window)',
      'cases':records}
    target=Path(__file__).resolve().with_name('ablation-receipt.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    for r in records:print(r['case'],'E - theta =',r['excess_over_theta'])

if __name__=='__main__':main()
