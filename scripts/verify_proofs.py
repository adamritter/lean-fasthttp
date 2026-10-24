#!/usr/bin/env python3
"""Fail closed on missing theorem audits, sorryAx, or nonstandard axioms."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    modules = sorted((ROOT / 'FastHTTP').glob('*Proofs.lean'))
    declared = set()
    for path in modules:
        source = path.read_text()
        declared.update('FastHTTP.Protocol.' + name for name in
            re.findall(r'^theorem\s+(\w+)', source, re.M))
    audit_file = ROOT / 'FastHTTP/ProofAudit.lean'
    audited = set(re.findall(r'^#print axioms\s+(\S+)', audit_file.read_text(), re.M))
    assert declared and declared == audited, {'missing':sorted(declared-audited), 'extra':sorted(audited-declared)}
    run = subprocess.run(['lake', 'env', 'lean', str(audit_file)], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert run.returncode == 0, run.stdout + run.stderr
    rows = {}
    for name, phrase, axioms in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", run.stdout):
        dependencies = set(filter(None, (a.strip() for a in axioms.split(','))))
        assert dependencies <= ALLOWED, (name, sorted(dependencies - ALLOWED))
        rows[name] = sorted(dependencies)
    assert set(rows) == declared, {'unaudited': sorted(declared-set(rows)), 'output':run.stdout}
    sources = [ROOT / 'FastHTTP.lean', *sorted((ROOT / 'FastHTTP').glob('*.lean'))]
    hashes = {str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in sources}
    print(json.dumps({'result':'PASS', 'theorems':len(rows), 'axioms':rows,
        'source_sha256':hashes, 'lean':subprocess.check_output(['lean','--version'], text=True).strip()}, indent=2))

if __name__ == '__main__':
    main()
