#!/usr/bin/env python3
"""Regression for the stale-installed-binary failure found during validation."""
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
import artifacts


def rejected(binary):
    try:
        artifacts.assert_current(binary)
    except AssertionError:
        return
    raise AssertionError('stale or unbound executable was accepted')


def main():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        manifest = root / 'bin/build-manifest.json'
        (root / 'bin').mkdir()
        (root / '.lake/build/bin').mkdir(parents=True)
        (root / '.lake/packages/lean_uv').mkdir(parents=True)
        source = root / 'Example.lean'
        dependency = root / '.lake/packages/lean_uv/Example.lean'
        source.write_text('def value := 1\n')
        dependency.write_text('def dependency := 2\n')
        for installed, built in artifacts.BINARIES.items():
            (root / 'bin' / installed).write_bytes(b'original executable')
            (root / '.lake/build/bin' / built).write_bytes(b'original executable')
        with patch.object(artifacts, 'ROOT', root), patch.object(artifacts, 'MANIFEST', manifest), \
             patch.object(artifacts.subprocess, 'check_output', return_value='synthetic-checkpoint'):
            artifacts.record(artifacts.source_digest())
            binary = root / 'bin/protocol-probe'
            assert artifacts.assert_current(binary)
            for changed in (source, dependency, binary, root / '.lake/build/bin/protocol_probe'):
                original = changed.read_bytes()
                changed.write_bytes(original + b'changed')
                rejected(binary)
                changed.write_bytes(original)
                assert artifacts.assert_current(binary)
            manifest.unlink()
            rejected(binary)
    print(json.dumps({'result': 'PASS', 'stale_source_dependency_copy_build_and_missing_manifest': 5}))


if __name__ == '__main__': main()
