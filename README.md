# lean-fasthttp

Experimental callback HTTP/1.1 server in Lean 4.35.0, with a pure protocol state
machine, built-in or per-worker lean-uv networking, prepared responses, streaming
output, and 115 kernel-checked feed, framing, header, numeric and URI properties. **Not a fully verified or
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

## Worker transport and verified body decoder (2026-10-24)

`FastHTTP.UV.serve` runs the complete HTTP parser and existing handler API on
four independent lean-uv workers in one process. The pinned dependency is tested
on Lean 4.26 and 4.35, including its C FFI under ASan/UBSan. The FastHTTP package
uses Lean 4.35. The implementation passes the same wire suites on both transports,
and four-worker tests additionally verify dynamic bodies, deferred replies,
pipelining, HEAD and half-close ordering.

The body decoder now has a terminating byte-machine reference and a fast bulk
implementation. Lean proves **the actual decoder's** arbitrary-fragment
composition, exact fixed-body contents, cursor bounds, pipeline-suffix preservation,
and equivalence of every bulk step and the complete loop to the reference.
The full `Protocol.feed` interface now also has a composition theorem for any
finite list of fragments. Equality includes the entire Request, its exact raw
header prefix, all metadata, body, trailers, Expect continuation and pipeline
remainder. The proof exposed and fixed fragment-dependent raw-buffer retention
and limit-error classification. All 115 theorems are audited for axioms. [Detailed formal scope](FORMAL_SCOPE.md)
distinguishes these guarantees from the still-unproved full RFC grammar and I/O
interpreter; this is not a full formal proof of HTTP/1.1 conformance.

The earlier measured production-code checkpoint
[`0fbd69b`](https://github.com/adamritter/lean-fasthttp/commit/0fbd69bbca866724d941dae29b3907fe4fd36ab2)
reaches **479,333 completed requests/s** (median of three 15-second runs), with
four I/O workers in one process restricted to four GH200 CPU cores. All three
runs exceed 400k/s: **472,558–493,836/s**. The timed clients verify the status,
Content-Length and complete 1 KiB body of **all 21,726,656 responses**, with zero
invalid responses. This is HTTP/1.1 keep-alive on Linux loopback, 256 connections,
eight client threads on separate CPUs, no pipelining and no TLS.

| Same complete HTTP parser/handler | 1 server CPU | 4 server CPUs |
|---|---:|---:|
| Original Std transport | 51,654 req/s | 41,198 req/s |
| lean-uv transport | 108,522 req/s | **479,333 req/s** |

The four-worker server consumes about 3.99 CPU seconds per wall second. It has
four I/O workers plus runtime/helper threads (12 observed OS threads total); the
entire process is restricted to CPUs 16–19. The Std four-CPU control uses one
shared I/O loop and four Lean scheduler threads. Fixed total concurrency means
per-worker connection counts differ across the scaling configurations.

A fresh final evaluation passes **23,554 exact-fragment cases**, including
10,000 newly generated pipelines and their random fragmentations, plus a new
four-worker dynamic-response corpus. The code checkpoint's CI passes.
[Verification manifest](results/2026-10-24-uv-final/verification.json),
[raw throughput and metadata](results/2026-10-24-uv-final-throughput/),
[formal scope](FORMAL_SCOPE.md).

The byte-only body decoder initially regressed 1 MiB echo throughput from about
513 to 52 MiB/s. Proved bulk-copy refinement restored approximately 534–536 MiB/s
in a three-repeat fixed/chunked echo comparison. This is a separate client/server
body benchmark, with Python validation included. The negative result and recovery
remain in [development evidence](results/2026-10-24-uv-integration/).

## Earlier single-loop checkpoint validation (2026-10-24)

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

The original Std transport has no idle deadline, connection cap or stop handle.
The lean-uv transport defaults to a 30-second read-idle timeout, a 4 MiB retained
write budget and 65,536 connections per worker, and supports signal shutdown.
It clears suspended continuations and releases active streams on native closure;
an application-owned producer task is not automatically cancelled. Both transports
require prompt callbacks and release hooks. A total header-completion deadline,
TLS and request-body streaming remain outside this buffered origin-server API.

## What is actually proved

`lake build FastHTTP.ProofAudit` checks 115 theorems
without `sorry`, custom axioms, `unsafe` or `native_decide`. The optimized runtime
scanner and decoder are proved equivalent to explicit references, not replaced
by an unproved `implemented_by` implementation. Proof terms are erased and do
not run per request. `scripts/verify_proofs.py` checks the complete theorem list
and permits only the standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`), or none. See [formal scope](FORMAL_SCOPE.md) and the checked-in
checkpoint audit for the exact statements and source hashes.

| Executable primitive | Kernel-checked property |
|---|---|
| `scanFeedFast` / `scanFeed` | Optimized scanner equals the fold for all states; agrees with an independent literal CRLFCRLF first-match/limit specification |
| `scanFeed` | Feeding two buffers equals feeding their concatenation; extends to any list of fragments |
| `scanByte` / `scanFeed` | Once the first delimiter offset is recorded, later bytes cannot change the scanner |
| `chooseFraming` | CL together with TE is rejected; an accepted fixed length is preserved |
| `takeCount` | Consumption is bounded by both remaining body and available bytes; remainder is conserved; fragmentation preserves counts |
| `takeBody` | Cursor stays within the input; extracted length is exact; consumed bytes plus suffix reconstruct the original bytes from the cursor; a complete body stops exactly at its declared end |
| `takeBody` | Fixed-body bytes consumed across two buffers equal the bytes consumed from their concatenation |
| `bodyFastLoop` | Every bulk payload step and the complete terminating loop equal the byte reference, for arbitrary buffers, states and cursors |
| `decodeBody` | Arbitrary-fragment composition preserves decoded body, trailers, rejection and the first boundary; fixed-length payload bytes are exact; appending any pipeline suffix cannot change a completed result |
| `decodeBody` | Successful stop cursors stay within the supplied input; consumed wire prefix and untouched suffix reconstruct the input exactly |
| `wireBody` / `responseLength` | HEAD/204/304 emit no body; 204 omits Content-Length; ordinary response declared lengths match emitted body size |

**These do not prove the whole server correct.** In particular, header/URI grammar acceptance, lexical correctness of chunk sizes/extensions/trailers,
composition of the complete `feed` across arbitrary inputs, decimal/hex wire
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

### lean-uv transport

`import FastHTTP.UV` provides `FastHTTP.UV.serve transport makeHandler config`.
`transport : LeanUV.TCP.Config` selects the address, worker count, CPU affinity,
idle timeout, connection limit and retained-write budget. `makeHandler` receives a
worker ID and constructs its `FastHTTP.Handler` inside that worker. Create mutable
application state in the factory; shared state needs synchronization.

```lean
import FastHTTP.UV

def main : IO Unit := do
  let _ ← FastHTTP.UV.serve { port := 8080, threads := 4 } fun _worker => do
    let response ← IO.ofExcept ((FastHTTP.Response.create "hello".toUTF8).mapError IO.userError)
    return fun _request => pure (.ready response)
```

Ready, deferred and streaming replies use the same parser, response framing and
handler types as `FastHTTP.serve`. No benchmark request bypasses validation.
Gather writes retain the original buffers. The adapter waits for outstanding
writes before reading another stream chunk or dispatching the next pipelined
request, and pauses reads while a promise is pending. Promise completion is
polled on the owner worker, at intervals up to approximately 10 ms. Stream cleanup
runs once on completion, failure or connection closure. Large individual replies
are split to fit the transport's bounded write budget. After 256 pipeline/stream
steps the continuation yields to the event loop.

Build `uv_http` / `uv_http_example`; `scripts/build.sh` installs them as
`bin/lean-uv-http` / `bin/lean-uv-http-example`. The benchmark accepts port,
worker count and optional first CPU. The example fixture defaults to one worker;
its state is deliberately independent per worker. The pinned lean-uv dependency
requires Linux, a C compiler and libuv headers (`libuv1-dev`).

Run the same wire suites with `FASTHTTP_BACKEND=uv`. `scripts/verify_uv.py` adds
four-worker tests with fresh random fixed/chunked bodies, deferred responses,
HEAD, connection close and half-close. `scripts/benchmark_uv.py` compares the
original transport with the worker transport using identical full HTTP parsing
and 1 KiB response bodies; it records raw runs, source/binary hashes, process CPU
usage, worker counters and client settings. Use `--validate-bodies` to check every timed response. Final repeated results
and exact reproduction commands are linked near the top of this README; earlier
short development runs remain separately labelled.
