#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
mkdir -p bin
cp .lake/build/bin/fast_http bin/lean-fast-http
cp .lake/build/bin/fast_http_example bin/lean-fast-http-example
cp .lake/build/bin/h1_http bin/lean-h1-http
cp .lake/build/bin/baseline_http bin/lean-fast-http-before
cp .lake/build/bin/v1_http bin/lean-fast-http-v1
