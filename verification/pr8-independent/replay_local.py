"""Fresh native compilation of an inventoried source closure, followed by kernel replay."""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
from pathlib import Path
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--inventory',type=Path,required=True);p.add_argument('--jobs',type=int,required=True);p.add_argument('--threads',type=int,required=True);a=p.parse_args()
root=Path(__file__).resolve().parent
inv=json.loads(a.inventory.read_text());lib=root/'.lake/build/lib/lean';logs=root/'logs';receipts=root/'compile-receipts.jsonl'
sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.now(timezone.utc).isoformat()
files={x['path'][4:-5].replace('/','.'):root/x['path'][4:] for x in inv['files']}
for x in inv['files']:assert sha((root/x['path'][4:]).read_bytes())==x['sha256']
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif s[i:i+2]=='--':
   end=s.find('\n',i);i=len(s) if end<0 else end
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
deps={}
for name,path in files.items():
 imports=[]
 for match in re.finditer(r'^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)',uncomment(path.read_text()),re.M):
  imports+=match[1].split()
 deps[name]=set(imports)&files.keys()
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for d in deps[n]:visit(d)
visit('Candidate.Main');assert seen==files.keys(),f'Closure differs: {len(seen)}/{len(files)}'
assert not list((lib/'Candidate').rglob('*.olean')) and not list((lib/'Submissions').rglob('*.olean')),'Fresh replay requires no old candidate objects'
lean=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin/lean'
leanchecker=lean.with_name('leanchecker')
lean_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(root/'private-home'),'TMPDIR':str(root/'tmp'),'LANG':'en_US.UTF-8','LEAN_PATH':lean_path,'LEAN_NUM_THREADS':str(a.threads)}
for d in ['private-home','tmp']:(root/d).mkdir(exist_ok=True)
report={'started_at':now(),'source_modules':len(files),'fresh_candidate_objects':True,'jobs':a.jobs,'threads_per_compiler':a.threads,'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'status':'running','native_mac_replay':True,'tracker_acceptance':False,'independent_external_kernels':False}
def save():(root/'replay-result.json').write_text(json.dumps(report,indent=2)+'\n')
save()
def compile_one(name):
 file=files[name];out=lib/Path(*name.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 log=logs/(name+'.log');started=now();t=time.monotonic()
 with log.open('w') as f:r=subprocess.run([str(lean),f'-j{a.threads}','-o',str(out),str(file.relative_to(root))],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 return {'module':name,'started_at':started,'completed_at':now(),'elapsed_seconds':round(time.monotonic()-t,3),'exit_code':r.returncode,'source_sha256':sha(file.read_bytes()),'log_sha256':sha(log.read_bytes()),'olean_sha256':sha(out.read_bytes()) if out.exists() else None}
pending=set(files);done=set();running={};failed=[]
with receipts.open('w') as f,concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
 while pending or running:
  if not failed:
   ready=sorted(n for n in pending if deps[n]<=done)
   for n in ready[:a.jobs-len(running)]:running[pool.submit(compile_one,n)]=n;pending.remove(n)
  if not running:
   if failed:break
   raise RuntimeError('Unresolved imports or dependency cycle')
  completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in completed:
   n=running.pop(future);r=future.result();f.write(json.dumps(r)+'\n');f.flush()
   if r['exit_code']!=0:failed.append(n);print('FAILED',n,r['exit_code'],flush=True)
   else:done.add(n)
   report.update(compiled_modules=len(done),failed_modules=failed);save()
   if len(done)%100==0:print('Compiled',len(done),'/',len(files),flush=True)
if failed:
 report.update(status='compilation-failed',completed_at=now());save();raise SystemExit(1)
# The target was compiled before the candidate and is deliberately a separate module.
for stage,cmd in [('endpoint',[str(lean),'-o',str(lib/'IndependentEndpoint.olean'),'IndependentEndpoint.lean']),('kernel-replay',[str(leanchecker),'--fresh','--verbose','IndependentEndpoint'])]:
 report['stage']=stage;save();print('Starting',stage,flush=True);t=time.monotonic()
 log=logs/(stage+'.log')
 with log.open('w') as f:r=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 report[stage]={'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'log_sha256':sha(log.read_bytes())};save()
 if r.returncode:report.update(status=stage+'-failed',completed_at=now());save();raise SystemExit(1)
 if stage=='endpoint':
  output=log.read_text();audits=re.findall(r"depends on axioms: \[([^\]]*)\]",output)
  allowed={'propext','Classical.choice','Quot.sound'}
  assert len(audits)==2 and all(set(x.strip() for x in v.split(','))<=allowed for v in audits),output
  report['allowed_axioms']=sorted(allowed);report['axiom_audit_passed']=True;save()
for x in inv['files']:assert sha((root/x['path'][4:]).read_bytes())==x['sha256']
report.update(status='passed',completed_at=now(),sources_unchanged=True);save();print('PASS: complete fresh source build, canonical endpoint, axiom audit, and Lean kernel replay',flush=True)
