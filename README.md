# lean-fasthttp

## Action handlers, streaming, SSE and cancellation

`FastHTTP.Action` adds inline IO/async completion and lazy cancellation scope
acquisition without a LeanIO dependency. Ready buffered results need no context
allocation or cancellation mutex operation; actual suspension, streams and
explicit context access acquire runtime state. This does not claim zero total
async overhead. See [Action](FastHTTP/Action.lean) and its
[proofs](FastHTTP/ActionProofs.lean).

Cancellable pending completions, streaming sources and SSE use the existing
response grammar and ownership model. Late streaming completions are released
when the request has already been cancelled. Native FFI and scheduler behavior
remain tested assumptions, not fully verified code. The vendored LeanUV copy
includes disconnect detection during suspended reads and write activity idle
accounting; see [vendor provenance](vendor/UPSTREAM.md).

The optional [LeanIO integration](https://github.com/adamritter/leanio-fasthttp)
provides direct IO and unified Action handlers, the real LeanIO route trie and
extractors, middleware, and buffered/streaming/SSE responses. It retains the
measured source checkpoints and validation logs. Its historical single-core
1-KiB GET medians were 86.6k/s Native, 89.6k/s Action and 93.2k/s direct IO
(5 x 10 seconds; overlapping ranges). These are routed dynamic-response
applications, distinct from the simpler prepared-response benchmarks below.


HTTP/1.1 in Lean 4.35.0, with prepared responses, asynchronous streaming and
independent lean-uv workers. The UV server has a **complete conditional proof of
its documented origin-server wire/framing model**: `http11_end_to_end` and
`driver_eventual_reply`. The audit checks **384 kernel theorems and four
certificate factories**, with no `sorry`, custom axioms or `native_decide`.

[Exact model, statements and assumptions](FORMAL_SCOPE.md) ·
[Top-level safety theorem](FastHTTP/EndToEndProofs.lean) ·
[Conditional liveness theorem](FastHTTP/DriverProgressProofs.lean)

## Build and run

Install Lean through [elan](https://github.com/leanprover/elan) and install libuv's
development headers. Linux wire tests use Python 3 and `taskset`.

```sh
scripts/build.sh
python3 scripts/verify_proofs.py
FASTHTTP_BACKEND=uv python3 scripts/verify_fast_protocol.py
FASTHTTP_BACKEND=uv python3 scripts/verify_rfc.py
python3 scripts/verify_uv.py
bin/lean-uv-http 18098 4
```

`FastHTTP` uses Lean 4.35. The vendored dependency starts from the pinned
[lean-uv](https://github.com/adamritter/lean-uv/commit/1d116e2a8c368ca932efbf6a16a6c8ef1e548596)
works on Lean 4.26 and 4.35, with both-version contract audits and native
ASan/UBSan regressions. Build artifacts are generated locally; every test and
benchmark rejects stale installed executables using source/dependency/binary
SHA-256 manifests.

## What is proved

The actual optimized scanner and body decoder equal their terminating reference
machines. The actual public parser accepts exactly `RequestWire`, including
method/target/authority, ordered header meaning, fixed/chunked bodies, binary
trailers, limits, Expect and untouched pipeline suffixes, under any fragmentation.

The deployed UV controller is a pure reactor. Its receive ledger ties every
handler request to unchanged bytes in the native input. Every observation prefix
has the correct pending operation and response grammar: HEAD never enters a body
producer phase, chunk writes wait for acknowledgments, and the terminal chunk
finishes before another pipelined request. Prepared responses, streaming heads
and Date buffers carry erased grammar certificates; even direct record
construction must provide the proof. Output fields cannot inject framing, Date,
CRLF or duplicate names, except repeatable Set-Cookie.

Under the explicit **generic** lean-uv execution, adapter, transport and
write-completion contracts, actual TCP output is an ordered prefix of the selected
bytes, acknowledged writes are complete, graceful close has exact output, and
actual finalizer invocations conserve adopted stream cleanup rights. The C FFI,
libuv, Lean compiler/runtime and OS are trusted through these visible theorem
parameters; their implementation is not a kernel proof. No HTTP correctness is
assumed from them.

Conditional progress additionally requires responsive I/O/application jobs and a
finite producer budget. A proved decreasing rank then yields final write
acknowledgment or an explicit interruption. Infinite SSE retains prefix safety;
an unresolved application promise cannot be given unconditional finite completion.
Clock truth/Std.Time calendar behavior and arbitrary application representation
metadata semantics are outside the wire proof. TLS, CONNECT tunnels, upgrades,
HTTP/2, caching and transparent decompression are outside the supported profile.

The retained Std backend shares the proved parser, constructors and stream policy
and passes the same wire tests. The complete IO-controller theorem specifically
covers `FastHTTP.UV.serve`.

## API

```lean
import FastHTTP.UV

def main : IO Unit := do
  let _ ← FastHTTP.UV.serve { port := 8080, threads := 4 } fun _ => do
    let reply ← IO.ofExcept ((FastHTTP.Response.create "hello".toUTF8).mapError IO.userError)
    return fun request => do
      if request.targetIs "/" then return .ready reply
      let echo ← IO.ofExcept ((FastHTTP.Response.create request.body).mapError IO.userError)
      return .ready echo
  pure ()
```

`Request.method`, `.target`, `.requestTarget`, `.authority`, `.header?`,
`.headerBytes?`, `.body`, `.rawTrailers`, `.close` and `.isHead` are available.
Body bytes remain binary and are buffered before dispatch. Header lookup is lazy
and ASCII case insensitive; trailers cannot replace the initial headers.

`Response.create body status reason contentType headers` prepares reusable
validated buffers. Header/Date/body gather writes share the payload. The UTC Date
cache refreshes once per monotonic second and checks the complete IMF-fixdate
wire syntax. Duplicate fields are rejected except Set-Cookie; callers combine
list-valued fields before construction. Managed Content-Type/framing/Date fields
cannot be overridden through custom prepared-response headers.

`Reply.ready` supplies a prepared response. `Reply.deferred` supplies its promise.
`Reply.streaming` uses `StreamResponse.create next release status reason headers`.
The producer returns a promise of `some nonemptyChunk` or `none` at EOF. Empty
chunks and producer errors abort. Each pull follows the previous successful write;
HEAD does not pull. The release hook runs exactly once for each adopted stream
right, including interruption. Hooks must return promptly; independently spawned
application tasks retain their own cancellation responsibilities.

## Supported profile and limits

HTTP/1.1 origin-form and absolute HTTP(S) targets, OPTIONS `*`, token methods,
required single valid Host, keep-alive, pipelining, Connection: close, HEAD,
fixed/chunked request bodies, chunk extensions, separate trailers and 100 Continue.
HTTP/1.0 responses close, with EOF framing for streams. Prepared final statuses
are 200..599; HEAD/204/205/304 obey body/length rules. Bodyless statuses cannot
create streams. HTTP/1.1 streaming uses chunked framing.

Malformed framing closes with 400; limits use 413/414/431, unsupported expectations
417, and unsupported CONNECT/schemes/codings 501 where applicable. Conflicting
CL/TE, duplicate Content-Length, repeated/nonfinal chunked coding, obsolete
folding and bare LF are rejected. Transfer-Encoding lines retain wire order.
One leading CRLF is accepted. Identical duplicate Content-Length rejection is an
intentional strict policy. Unknown methods reach the application.

Defaults: 16 KiB head, 8 KiB target, 1 MiB decoded body, 1 KiB chunk/trailer line,
16 KiB trailer section and 65,536 data chunks. UV defaults include a 30-second
read-idle timeout, 4 MiB retained-write budget and 65,536 connections per worker.
It supports signal shutdown. A total header deadline and request-body streaming
are not provided by this buffered API.

## Final checkpoint results

The final source [`db97763`](https://github.com/adamritter/lean-fasthttp/commit/db977633ade3d3a55cbffc55130c0c150fc48f7c)
passes 29,984 exact-fragment cases with a fresh seed, both transports' wire suites,
and 993 fresh four-worker integration responses. The kernel audit checks
384 theorems and the four certificate factories.

On GH200, **413,594 completed requests/s** is the median of three
15-second runs with four I/O workers and the whole server pinned to four CPUs.
All runs exceed 400k/s (**402,828–417,212/s**).
The timed clients checked all **18,540,879** complete 1 KiB response bodies,
with zero invalid responses. This uses loopback HTTP/1.1 keep-alive, 256
connections, eight client threads on separate CPUs, no TLS and no pipelining.
There are 12 OS threads including runtime helpers, all restricted to four server
CPUs. Proof terms are erased; constructor validation still executes normally.

[Final verification and assumptions](results/2026-10-24-end-to-end-history-final/) ·
[All throughput runs and metadata](results/2026-10-24-end-to-end-history-throughput/)

## Reproduce validation and throughput

```sh
scripts/build.sh
python3 scripts/verify_artifacts.py
python3 scripts/verify_proofs.py
python3 scripts/verify_generated.py --cases 10000 --seed 20261025
python3 scripts/verify_fast_protocol.py
python3 scripts/verify_rfc.py
FASTHTTP_BACKEND=uv python3 scripts/verify_fast_protocol.py
FASTHTTP_BACKEND=uv python3 scripts/verify_rfc.py
python3 scripts/verify_uv.py
python3 scripts/benchmark_uv.py --wrk /path/to/wrk --validate-bodies \
  --seconds 15 --warmup 3 --repeats 3 --first-cpu 16 \
  --client-cpus 24-31 --configs uv:4 --output results/new-run
```

Use available disjoint server/client CPUs on your host. `FASTHTTP_TEST_CPU`
overrides the wire-test CPU. Throughput measures completed, validated responses,
not parser-only operations. All timings are host/workload-specific.

[Historical measurements and negative results](HISTORY.md) preserve earlier
checkpoints. In particular the pure reactor costs about 13% throughput against
the earlier callback controller on GH200, while the preceding pure-reactor
checkpoint still exceeded 400k/s in all three runs. The native cleanup diagnostic
also preserves the old yield-related leak and its corrected immediate-finalizer
regression in the pinned lean-uv repository.

### Ready-only SSE batching

SSE coalesces immediately available chunks, with a default budget of 32 pulls
and 16 KiB per batch. The byte budget is checked after each indivisible chunk.
An unresolved next pull never delays already buffered bytes; it is retained for
the next call. EOF, errors and invalid empty chunks are preserved. Cleanup remains
owned by the existing cancellation/stream adapter. Applications can also use
`AsyncStream.Source.batchReady` explicitly. This is bounded read-ahead, so a source
may be pulled up to one batch before the corresponding socket write completes.

Five kernel theorems in `BatchProofs.lean` prove byte and length conservation and
invariance under regrouping completed chunks. They do not prove task scheduling or
the C transport. Tests cover readiness, one outstanding pull, ordered delivery,
batch limits, EOF, failure and cancellation. Genuine suspended transport work still
uses the existing 10 ms polling adapter; this change does not make it event-driven.

The single-line SSE data fast path also has a kernel-checked wire-form theorem.
Multiline data retains CRLF/CR normalization; 9,330 encoder cases compare the
optimized encoder with the line-normalizing reference, including Unicode and NUL.
