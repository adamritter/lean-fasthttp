# lean-fasthttp

Experimental callback HTTP/1.1 server in Lean 4.35.0, with a pure protocol state
machine, built-in libuv networking, prepared responses, streaming output, and
29 kernel-checked framing/response properties. **Not a fully verified or
production-ready HTTP implementation.**

```sh
scripts/build.sh
python3 scripts/verify_fast_protocol.py
python3 scripts/verify_proofs.py
bin/lean-fast-http 18095
```

Install Lean via [elan](https://github.com/leanprover/elan). Wire tests require
Linux, Python 3 and `taskset`; throughput measurement additionally requires
[wrk](https://github.com/wg/wrk) in PATH (or `WRK=/path/to/wrk`). Build artifacts
and benchmark executables are not checked in. `FASTHTTP_TEST_CPU` overrides the
test server’s CPU affinity; the benchmark defaults to server CPU 0 and clients
on CPUs 4–11.

## Current checkpoint validation (2026-10-24)

[Verification manifest](results/2026-10-24-rfc/verification.json) for source
[`078d75d`](https://github.com/adamritter/lean-fasthttp/commit/078d75d645e29e1e1ce0e4d9bf1ee84292c65148):
29 audited Lean theorems, 4,245 maintained exact-fragment cases, and a final
12,245-case evaluation with a new seed, including 5,000 generated request pipelines.
Socket regressions and [GitHub CI](https://github.com/adamritter/lean-fasthttp/actions/runs/40099396661) passed.
The final corpus and executable hashes are recorded. The formal proof scope is
partial; the complete header/chunked parser and networking interpreter remain
unproved. Passing the test corpus does not turn these into formal theorems.

Same-host medians from 3 × 15 seconds, 64 connections, one allocated server CPU,
8 wrk threads on disjoint CPUs, 1024-byte prepared replies, Linux loopback on a
shared Lambda GH200 host (CPU measurement):

| Variant | Requests/second |
|---|---:|
| Exact original `ad80f25` | 61,124.90 |
| Expanded HTTP/1.1 implementation `078d75d` | 58,096.77 |

The expanded implementation is 4.95% slower on this workload and includes
additional grammar checks and fresh Date headers. Its samples ranged from
53,748.58 to 58,972.68 requests/second.
All six timed runs passed socket/status and suspend/timing checks.
[Raw final measurements](results/2026-10-24-rfc-checkpoint-throughput/summary.json),
[first comparison](results/2026-10-24-rfc-throughput/summary.json), and
[intermediate comparison](results/2026-10-24-rfc-final-throughput/summary.json)
are retained. These measurements do not establish a network throughput gain
from the scanner or callback changes. The scanner's early exit and its semantic
equivalence are proved; its isolated timing was not measured. Kernel permissions
prevented profiling, so no hotspot attribution is claimed. Zero VmHWM readings
were unavailable measurements, not zero memory usage.

## Historical workstation throughput

Same-run medians from 3 × 15 seconds, 64 connections, one allocated server CPU,
8 wrk threads, 1024-byte prebuilt responses, Linux loopback:

| Variant | Requests/second |
|---|---:|
| Original GET-only callback baseline | 48,123 |
| First expanded protocol implementation | 45,135 |
| Optimized expanded callback implementation | **50,924** |
| Unmodified Std H1 reader/writer with callback transport | 23,966 |

[Raw runs, timing checks and metadata](results/2026-10-24/summary.json).
All 12 final runs passed socket/status checks and suspend detection. One earlier
batch was interrupted by host suspend and is excluded. The optimized version
was 12.8% faster than the first expanded version in this comparison. The H1
variant supports a different and broader protocol profile, and serializes
response headers per request; this is not a claim of equal feature coverage.
These are shared-workstation measurements, not isolated-host guarantees.

The numbers were collected in the original `http-bench` workspace before
packaging this repository. Original executable hashes, commands and paths are
retained as provenance. The server sources are copied unchanged; benchmark
baseline namespaces and entrypoint module names were adjusted for this
standalone package. Rebuilt binaries can therefore have different hashes.

## API and implementation

```lean
import FastHTTP

def main : IO Unit := do
  let addr : Std.Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 8080⟩
  let reply ← IO.ofExcept ((FastHTTP.Response.create "hello".toUTF8).mapError IO.userError)
  FastHTTP.serve addr fun request => do
    if request.targetIs "/" then return .ready reply
    let echo ← IO.ofExcept ((FastHTTP.Response.create request.body).mapError IO.userError)
    return .ready echo
```

`Request.method`, `.target`, `.targetIs`, `.header?`, `.body`, `.trailers`,
`.close` and `.isHead` are available. Headers retain the original receive bytes;
lookup is lazy, ASCII case insensitive and returns the first matching field.
Trailers are separate and cannot replace request headers. Body bytes are never
converted to text. Request bodies are buffered before invoking the handler.

`Response.create body status reason contentType headers` validates response
fields and prepares reusable wire buffers, including HEAD and connection-close
variants. Applications cannot override framing fields or the managed Date field with custom headers.
A per-server UTC Date cache refreshes at most once per monotonic second; even
indefinitely reused prepared responses receive a fresh Date. Header, Date, and
payload buffers are shared through gather writes without copying the payload.
Repeated non-framing fields such as Set-Cookie are preserved. This path still
serializes **once when the response is constructed**, not on every request.

`Reply.ready` returns immediately. `Reply.deferred` takes a promise of a prepared
response, allowing other connections to progress. `Reply.streaming` takes a
`StreamResponse` with a per-request `next` producer and a `release` hook.
The producer returns a promise of `some nonemptyChunk` or `none` at EOF. Each
chunk is requested only after the preceding write completes. It is encoded
without copying its payload, using a gather write. Producer errors after the
headers close the connection; they do not emit a second status line or dispatch
subsequent pipelined requests. The release hook runs on EOF, producer/write
failure, or HEAD suppression. An empty chunk is a producer error, not EOF.

Files:

- [Protocol.lean](FastHTTP/Protocol.lean): pure header/framing/body state
  machine. `feed` produces `need`, `continue`, `request`, or `reject` actions.
- [Response.lean](FastHTTP/Response.lean): validated prepared response writer.
- [Stream.lean](FastHTTP/Stream.lean): pull-producer API and chunk encoding.
- [FastHTTP.lean](FastHTTP.lean): UV callback interpreter. A connection resumes
  input processing only after its response write/stream completes.
- [Proofs.lean](FastHTTP/Proofs.lean): kernel-checked properties of executable
  protocol primitives, kept out of the server's runtime import graph.
- [FastExample.lean](Tests/Server.lean): executable API/regression examples.

## Supported HTTP profile

HTTP/1.1 origin-form and absolute HTTP(S) requests, OPTIONS `*`, token methods including POST/PUT/
PATCH/DELETE and extension methods, required single syntactically valid Host, keep-alive,
pipelining, Connection: close, HEAD, fixed and chunked request bodies, chunk
extensions, separate trailers, and automatic 100 Continue. HTTP/1.0 requests receive HTTP/1.0 responses and close after the response;
streamed HTTP/1.0 bodies use EOF framing. Final prepared
responses support 200..599, with body suppression and Content-Length rules for
HEAD/204/205/304. Streaming responses use chunked transfer coding.

Malformed requests receive 400 and close; resource limits use 413/414/431,
unsupported expectations 417, CONNECT 501. Upgrade offers are ignored. Conflicting CL/TE, duplicated
Content-Length or repeated chunked codings, malformed transfer-coding lists, obsolete folding and bare LF are
rejected. Transfer-Encoding field lines are combined in wire order. Unsupported codings
before a final chunked coding return 501;
a final non-chunked coding returns 400. One leading CRLF is accepted.
Rejecting duplicated identical Content-Length values is an intentional
strict policy. Unknown methods are dispatched to the application.

Defaults: 16 KiB request head, 8 KiB request target, 1 MiB decoded request body, 1 KiB per chunk-size or
trailer line, 16 KiB trailer section, 65536 data chunks (the terminal zero chunk does not count). These limits are configurable.
Header/trailer fields and chunk metadata cannot cause unbounded integer growth.

This is **not a complete RFC-conforming or production-ready HTTP server**.
The protocol rules were checked against [RFC 9112](https://www.rfc-editor.org/rfc/rfc9112.html)
and [RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html), but the current profile
does not implement CONNECT tunnels or protocol upgrades. Request targets validate URI characters and percent
escapes; Host validates reg-name, bracketed IPv6/IPvFuture, and decimal port syntax.
Absolute HTTP(S) targets route by path/query; other syntactically valid URI
schemes receive 501 after header/framing validation. `requestTarget` retains the wire
form and `authority` uses the URI authority, ignoring Host for absolute targets.
`rawTrailers` and `headerBytes?` preserve non-UTF-8 field values. The text
`trailers` view decodes UTF-8 where possible, otherwise maps octets to Latin-1. There is no transparent decompression or application caching logic.

Lifecycle work also remains: no header/idle deadlines, active connection limit,
server shutdown handle, TLS, or request-body streaming API. A promise that never
resolves keeps that connection pending; peer disconnect does not cancel an
application promise or pending stream producer. The release hook therefore
cannot guarantee prompt cleanup while a producer is permanently pending.
Callbacks and release hooks must return promptly. These are explicit remaining
items, not properties established by the current tests or proofs.

## What is actually proved

`lake build FastHTTP.Proofs` checks 29 theorems without `sorry`, custom axioms,
`unsafe`, or `native_decide`. They refer to the **functions used by this server**,
not a separate idealized HTTP implementation. The proof terms are erased and
are not executed per request. The [current axiom audit](results/2026-10-24-rfc/proof-audit.json)
contains only the usual Lean axioms (`propext`, `Classical.choice`, `Quot.sound`),
or no axioms; no `sorryAx` or custom verification assumption is present.

| Executable primitive | Kernel-checked property |
|---|---|
| `scanFeedFast` / `scanFeed` | Optimized scanner equals the fold for all states; agrees with an independent literal CRLFCRLF first-match/limit specification |
| `scanFeed` | Feeding two buffers equals feeding their concatenation; extends to any list of fragments |
| `scanByte` / `scanFeed` | Once the first delimiter offset is recorded, later bytes cannot change the scanner |
| `chooseFraming` | CL together with TE is rejected; an accepted fixed length is preserved |
| `takeCount` | Consumption is bounded by both remaining body and available bytes; remainder is conserved; fragmentation preserves counts |
| `takeBody` | Cursor stays within the input; extracted length is exact; consumed bytes plus suffix reconstruct the original bytes from the cursor; a complete body stops exactly at its declared end |
| `takeBody` | Fixed-body bytes consumed across two buffers equal the bytes consumed from their concatenation |
| `wireBody` / `responseLength` | HEAD/204/304 emit no body; 204 omits Content-Length; ordinary response declared lengths match emitted body size |

**These do not prove the whole server correct.** In particular, header grammar acceptance, the entire chunked
state machine, composition of `feed` across arbitrary inputs, decimal/hex wire
formatting, stream ordering/cancellation/liveness, and the UV interpreter remain
tested rather than fully verified. The byte-slicing theorems assume a valid input
cursor; the driver establishing that precondition everywhere is not yet proved.
The Lean kernel, compiler/runtime, native ByteArray implementations, libuv and OS
remain in the trusted base. No claim of end-to-end RFC conformance is made.

## Reproduce validation and throughput

```sh
scripts/build.sh
python3 scripts/verify_fast_protocol.py
python3 scripts/benchmark.py \
  --configs lean-fast-before-1 lean-fast-1 --seconds 15 --repeats 3 \
  --connections 64 --output new-run
```

An interrupted comparison is preserved in `results/interrupted`:
the kernel journal recorded host s2idle suspend/resume and wrk reported 64
timeouts with a 32-second duration for a 15-second run. That incomplete batch
is excluded. The final batch uses both monotonic and boot clocks to reject
suspend-affected or excessively long measurements, in addition to all socket
and HTTP error checks.

The `before` executable is the preserved previous GET-only build; its source is
`Bench/Baseline.lean`. Existing historical benchmark
results are immutable. New measurements record binary SHA-256 hashes, commands,
CPU allocation and raw wrk output. All measured servers use CPU 0 and one Lean worker;
wrk uses CPUs 4–11 with 8 threads and 64 connections. Payloads are the same
prebuilt 1024 bytes. Results are from a shared workstation, not an isolated host.

Wire tests cover every split and one-byte fragmentation of representative fixed
and chunked requests, binary bodies through 1 MiB, 100 Continue, trailers,
HEAD/204/205/304, response headers, asynchronous replies, 1280 concurrent
pipelined POSTs, 8192 queued responses, disconnect churn, 33 malformed/error
cases, and an 8 MiB chunked stream with a delayed reader, HEAD suppression,
producer failure and release-count checks. These are regression evidence, not
formal proofs of those complete features.

## Current verification additions

`python3 scripts/verify_generated.py` drives the actual pure parser through a
compiled test-only probe with exact fragments (including empty and single-octet
fragments). Seed 20261024 covers 4,245 cases from 1,000 generated binary-body
pipelines, every split of representative messages, malformed framing, version
rules, connection closure, and exact limits. Expected messages are generated
independently in Python. These are component regressions, not a whole-protocol
formal proof. `scripts/verify_rfc.py` separately covers actual socket behavior.
CI checks all three suites and fails on any unaudited theorem or unexpected axiom.

To rebuild the original comparison binary from its exact source commit:

```sh
python3 scripts/build_original.py
python3 scripts/benchmark.py --configs lean-fast-original-1 lean-fast-1 --output comparison
```

The original comparison lacks the new grammar checks and Date header. Equal
payload, CPUs, connections and durations do not imply equal feature coverage.

## Profiling and optimization

A 12-second `perf` sample of the first expanded version, under 64-connection wrk
load, found 8.60% of sampled user CPU in the inner header parsing loop and 19.79%
in `lean_dec_ref_cold` plus `lean_alloc_small_object_core`. The latter are shared
runtime costs, **not** a measured attribution of all allocations to the parser.
Lean call-stack unwinding was incomplete, so inclusive allocation attribution is
not reliable. These profile percentages are user CPU sample shares, not shares
of wall time or request latency. [Raw reports](results/profile-v1.txt)
are retained; profiled throughput is not the headline
benchmark.

The final header scanner uses a tail-recursive loop with one header state record,
updating fields at header boundaries instead of carrying nested mutable-variable
tuples through every byte. The delimiter step is inlined. Bodyless requests
bypass construction and execution of an empty body decoder. No protocol checks
were removed. The first expanded binary is preserved as `lean-fast-http-v1` for
a same-run comparison. All protocol/streaming regressions and the original 19 proofs
were rerun after these changes.
