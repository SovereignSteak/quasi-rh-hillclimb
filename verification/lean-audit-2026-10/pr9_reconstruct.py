# Independent re-implementation of Argonaut's reconstruct.py (reviewed): verify archive, compare dependency files to existing pinned clones, extract project files.
import json,hashlib,zipfile,sys
from pathlib import Path,PurePosixPath
root=Path('/home/claude/work/pr9/Lean_Proof'); proj=Path('/home/claude/work/pr9/project'); proj.mkdir(exist_ok=True)
m=json.loads((root/'provenance/SOURCE-MANIFEST.json').read_bytes())
arch=root/m['archive_path']; d=lambda b: hashlib.sha256(b).hexdigest()
assert d(arch.read_bytes())==m['archive_sha256']
pkgsrc={'PrimeNumberTheoremAnd':Path('/home/claude/work/pr8build/.lake/packages/PrimeNumberTheoremAnd'),'rellich-kondrachov':Path('/home/claude/work/pr8build/.lake/packages/rellich-kondrachov')}
inv=Path('/home/claude/work/invcap/.lake/packages')
stats={}
with zipfile.ZipFile(arch) as z:
    assert set(z.namelist())=={r['path'] for r in m['files']}
    for r in m['files']:
        b=z.read(r['path']); assert d(b)==r['sha256'] and len(b)==r['bytes']
        p=PurePosixPath(r['path']); assert not p.is_absolute() and '..' not in p.parts
        if p.parts[0]=='project':
            out=proj.joinpath(*p.parts[1:]); assert out.resolve().is_relative_to(proj.resolve())
            out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(b)
        elif p.parts[0]=='dependencies':
            pkg=p.parts[1]; base=pkgsrc.get(pkg, inv/pkg); f=base.joinpath(*p.parts[2:])
            k=(pkg,'same' if f.exists() and f.read_bytes()==b else ('differs' if f.exists() else 'missing'))
            stats[k]=stats.get(k,0)+1
            if k[1]!='same' and stats[k]<=3: print('  ',k,'/'.join(p.parts[2:]))
for k,v in sorted(stats.items()): print(v,*k)
