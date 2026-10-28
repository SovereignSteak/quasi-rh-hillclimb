import json,subprocess,concurrent.futures
from pathlib import Path
root=Path('/home/claude/work/pr9'); proj=root/'project'
pins=json.loads((root/'Lean_Proof/provenance/PINS.json').read_text())['locked_dependencies']
inv=Path('/home/claude/work/invcap/.lake/packages'); p8=Path('/home/claude/work/pr8build/.lake/packages')
def rev(p): return subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
def one(pin):
    n=pin['name']; dst=proj/'.lake/packages'/n
    if dst.exists() or dst.is_symlink(): return n,'exists'
    for src in [p8/n, inv/n]:
        if src.exists() and rev(src)==pin['revision']:
            patched=bool(subprocess.check_output(['git','-C',str(src),'status','--porcelain'],text=True).strip())
            if patched != (proj/'patches'/f'{n}-lean4341.patch').exists(): continue
            dst.parent.mkdir(parents=True,exist_ok=True); dst.symlink_to(src.resolve()); return n,f'shared({src.parent.parent.parent.name},patched={patched})'
    dst.mkdir(parents=True)
    for a in [['init','-q',str(dst)],['-C',str(dst),'remote','add','origin',pin['url']],['-C',str(dst),'fetch','-q','--depth=1','origin',pin['revision']],['-C',str(dst),'checkout','-q','--detach','FETCH_HEAD']]:
        subprocess.run(['git',*a],check=True)
    assert rev(dst)==pin['revision']
    pf=proj/'patches'/f'{n}-lean4341.patch'
    if pf.exists():
        subprocess.run(['git','-C',str(dst),'apply',str(pf)],check=True); return n,'cloned+patched'
    return n,'cloned'
with concurrent.futures.ThreadPoolExecutor(4) as ex:
    for r in ex.map(one,pins): print(*r,flush=True)
