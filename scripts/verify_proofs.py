#!/usr/bin/env python3
"""Fail closed on missing theorem audits, sorryAx, or nonstandard axioms."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
CERTIFICATE_FACTORIES = {
    'FastHTTP.checkedResponseFields', 'FastHTTP.Response.create',
    'FastHTTP.StreamResponse.create', 'FastHTTP.DateHeader.create',
}


def main():
    modules = sorted((ROOT / 'FastHTTP').glob('*Proofs.lean'))
    declared = set()
    for path in modules:
        source = path.read_text()
        namespace = re.search(r'^namespace\s+(\S+)', source, re.M)[1]
        declared.update(namespace + '.' + name for name in
            re.findall(r'^theorem\s+(\w+)', source, re.M))
    theorem_count = len(declared)
    declared.update(CERTIFICATE_FACTORIES)
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
    print(json.dumps({'result':'PASS', 'theorems':theorem_count, 'certificate_factories':sorted(CERTIFICATE_FACTORIES), 'axioms':rows,
        'top_level_safety_theorem':'FastHTTP.Protocol.http11_end_to_end',
        'liveness_theorem':'FastHTTP.Protocol.driver_eventual_reply',
        'explicit_native_hypotheses':['Machine.ExecutionContract','Machine.AdapterContract','Contract.NativeContract','Machine.CompletionContract'],
        'explicit_progress_hypotheses':['Machine.ResponsiveContract','FastHTTP.Protocol.FiniteProducerBudget'],
        'native_implementation_proved':False, 'http_correctness_assumed':False,
        'source_sha256':hashes, 'lean':subprocess.check_output(['lean','--version'], text=True).strip()}, indent=2))

if __name__ == '__main__':
    main()
