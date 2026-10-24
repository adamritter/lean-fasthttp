#!/usr/bin/env python3
"""Rebuild the exact pre-change callback server for same-host comparison."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = 'ad80f25fd47cfde93db96c76affe983ac565b1f0'


def main():
    with tempfile.TemporaryDirectory(prefix='fasthttp-original-') as directory:
        root = Path(directory)
        archive = root / 'source.tar'
        with archive.open('wb') as out:
            subprocess.run(['git','archive',ORIGINAL],cwd=ROOT,stdout=out,check=True)
        source = root / 'source'; source.mkdir()
        with tarfile.open(archive) as contents:
            contents.extractall(source, filter='data')
        subprocess.run(['lake','build','fast_http'],cwd=source,check=True)
        target = ROOT / 'bin/lean-fast-http-original'; target.parent.mkdir(exist_ok=True)
        shutil.copy2(source / '.lake/build/bin/fast_http',target)
        print(json.dumps({'source_commit':ORIGINAL, 'binary':str(target),
            'sha256':hashlib.sha256(target.read_bytes()).hexdigest()},indent=2))

if __name__ == '__main__':
    main()
