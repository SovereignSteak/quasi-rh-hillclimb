import concurrent.futures,json,os,subprocess,urllib.request
from pathlib import Path
root=Path(__file__).resolve().parent
manifest=json.loads((root/'lake-manifest.json').read_text())
packages=root/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
patches=root/'dependency-patches';patches.mkdir(exist_ok=True)
revision='ac76d5ef6008d976a7b8f3c1d921af2317e79ce9'
def clone(p):
 name=p['name'].strip('«»');dest=packages/name
 with (root/'logs'/('setup-'+name+'.log')).open('w') as log:
  def run(*args):subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,check=True)
  run('git','init',str(dest));run('git','-C',str(dest),'remote','add','origin',p['url'])
  run('git','-C',str(dest),'fetch','--depth=1','origin',p['rev'])
  run('git','-C',str(dest),'checkout','--detach','FETCH_HEAD')
  assert subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()==p['rev']
  if name in ['rellich-kondrachov','PrimeNumberTheoremAnd']:
   patch=patches/(name+'-lean4341.patch')
   patch.write_bytes(urllib.request.urlopen(f'https://raw.githubusercontent.com/HaileyStorm/QuasiRiemannTracker/{revision}/verifier/actions/patches/{patch.name}').read())
   run('git','-C',str(dest),'apply',str(patch))
 print('Pinned dependency ready:',name,flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:list(pool.map(clone,manifest['packages']))
print('All pinned sources ready',flush=True)
