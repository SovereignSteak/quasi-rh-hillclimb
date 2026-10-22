#!/usr/bin/env python3
"""Check bundled bytes and receipt consistency; does not run a proof checker."""
import hashlib
import json
from pathlib import Path
import zipfile

root = Path(__file__).resolve().parent.parent
sha = lambda data: hashlib.sha256(data).hexdigest()
expected = {}
for line in (root / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    path = root / name
    assert path.resolve().is_relative_to(root), name
    assert sha(path.read_bytes()) == digest, name
    expected[name] = digest
actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name != 'SHA256SUMS'}
assert actual == set(expected), 'Missing or unlisted package file'
inventory = json.loads((root / 'verification/source-inventory.json').read_text())
assert sha((root / 'lean-sources.zip').read_bytes()) == inventory['archive_sha256']
with zipfile.ZipFile(root / 'lean-sources.zip') as archive:
    sources = {name for name in archive.namelist() if name.startswith('src/') and name.endswith('.lean')}
    assert len(sources) == inventory['module_count'] == 6471
    assert sources == {item['path'] for item in inventory['files']}
    for item in inventory['files']:
        assert sha(archive.read(item['path'])) == item['sha256'], item['path']
closure = json.loads((root / 'verification/resumed-closure.json').read_text())
assert closure['missing_modules_completed_exit0'] == 40
assert len(closure['receipts']) == 41
for receipt in closure['receipts']:
    assert receipt['exit_code'] == 0 and receipt['stop'] is None
    log = root / 'verification/logs' / (receipt['module'] + '.log')
    assert sha(log.read_bytes()) == receipt['log_sha256']
audit = (root / 'verification/logs/RecoveryCandidateAudit.log').read_text()
assert audit.strip() == "'Candidate.bound' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert sha((root / 'verification/CandidateAudit.lean').read_bytes()) == closure['receipts'][-1]['source_sha256']
print('PASS: package hashes, all 6471 archived source hashes, 41 successful receipt/log bindings and final axiom output.')
print('Integrity/development evidence only; no fresh Lean or independent endpoint replay was run by this script.')
