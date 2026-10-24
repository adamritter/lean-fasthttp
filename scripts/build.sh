#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build_source_digest=$(python3 scripts/artifacts.py source-digest)
lake build
mkdir -p bin
cp .lake/build/bin/fast_http bin/lean-fast-http
cp .lake/build/bin/fast_http_example bin/lean-fast-http-example
cp .lake/build/bin/h1_http bin/lean-h1-http
cp .lake/build/bin/baseline_http bin/lean-fast-http-before
cp .lake/build/bin/v1_http bin/lean-fast-http-v1
cp .lake/build/bin/protocol_probe bin/protocol-probe
cp .lake/build/bin/uv_http bin/lean-uv-http
cp .lake/build/bin/uv_http_example bin/lean-uv-http-example
python3 scripts/artifacts.py record "$build_source_digest"
