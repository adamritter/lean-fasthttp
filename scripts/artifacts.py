#!/usr/bin/env python3
"""Bind installed executables to the checked build inputs; fail on stale copies."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'bin/build-manifest.json'
BINARIES = {
    'lean-fast-http': 'fast_http', 'lean-fast-http-example': 'fast_http_example',
    'lean-h1-http': 'h1_http', 'lean-fast-http-before': 'baseline_http',
    'lean-fast-http-v1': 'v1_http', 'protocol-probe': 'protocol_probe',
    'lean-uv-http': 'uv_http', 'lean-uv-http-example': 'uv_http_example',
}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def source_hashes():
    sources = {}
    # The patched dependency is vendored under ROOT and traversed with it.
    roots = [(ROOT, '')]
    for root, prefix in roots:
        for directory, dirs, files in os.walk(root):
            dirs[:] = [d for d in dirs if d not in ('.git', '.lake', 'bin', 'results', '__pycache__')]
            for name in files:
                path = Path(directory) / name
                if path.suffix in ('.lean', '.c', '.h') or name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    sources[prefix + str(path.relative_to(root))] = sha(path)
    return dict(sorted(sources.items()))


def source_digest(sources=None):
    return hashlib.sha256(json.dumps(source_hashes() if sources is None else sources, sort_keys=True).encode()).hexdigest()


def record(before):
    sources = source_hashes()
    assert source_digest(sources) == before, 'source changed during build; run scripts/build.sh again'
    binaries = {}
    for installed, built in BINARIES.items():
        actual = sha(ROOT / 'bin' / installed)
        assert actual == sha(ROOT / '.lake/build/bin' / built), installed
        binaries[installed] = actual
    MANIFEST.write_text(json.dumps({'source_sha256': sources, 'binary_sha256': binaries,
        'git_commit_at_build': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()}, indent=2) + '\n')


def assert_current(binary):
    binary = Path(binary).resolve()
    # Historical/custom executables are explicit caller choices and have their
    # own recorded hashes; the check applies to this repository's installed set.
    if binary.parent != ROOT / 'bin' or binary.name not in BINARIES:
        return False
    assert MANIFEST.exists(), 'missing build manifest; run scripts/build.sh'
    manifest = json.loads(MANIFEST.read_text())
    assert manifest['source_sha256'] == source_hashes(), 'source changed since build; run scripts/build.sh'
    expected = manifest['binary_sha256'][binary.name]
    assert sha(binary) == expected, 'installed executable changed; run scripts/build.sh'
    assert sha(ROOT / '.lake/build/bin' / BINARIES[binary.name]) == expected, 'installed executable is stale; run scripts/build.sh'
    return True


if __name__ == '__main__':
    if sys.argv[1] == 'source-digest': print(source_digest())
    elif sys.argv[1] == 'record': record(sys.argv[2])
    else: raise SystemExit('expected source-digest or record')
