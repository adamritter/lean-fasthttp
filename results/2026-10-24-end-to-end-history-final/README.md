# Final evaluated checkpoint

Source: `db977633ade3d3a55cbffc55130c0c150fc48f7c`. Pinned lean-uv:
`1d116e2a8c368ca932efbf6a16a6c8ef1e548596`.

All nine final checks passed after rebuilding this exact commit. The verification
manifest records every command, exit status, source/dependency/binary hash and
fresh corpus seed. The public README API example also typechecks.

- 362 kernel theorems and four certificate factories pass the axiom audit.
- 29,984 exact-fragment cases, including 10,000 fresh generated pipelines.
- Fresh generated seed: `951687582799365700`.
- Both Std and UV protocol/RFC wire suites pass.
- 993 fresh four-worker integration responses pass, including deferred
  handlers, dynamic binary streams, HEAD, close/half-close, pipeline ordering and
  per-worker exactly-once cleanup. Seed: `13229804275681599314`.

The complete conditional controller theorem covers the UV backend. The native
assumptions and application termination premises are explicit in
[formal scope](../../FORMAL_SCOPE.md); the C/libuv implementation is not claimed as
a kernel proof. The retained Std backend has shared component proofs and wire
regressions, without a separate full IO refinement theorem.

## Throughput on this exact source

[Raw data and metadata](../2026-10-24-end-to-end-history-throughput/) report
three 15-second runs after separate 3-second warmups. The server has four I/O
workers, with the whole process restricted to GH200 CPUs 16–19. The wrk client
uses eight threads on CPUs 24–31 and 256 persistent connections. The actual
HTTP parser/handler serves prepared 1 KiB bodies over loopback, without TLS or
HTTP pipelining. All timed responses validate status, framing and full body.

| Repeat | Requests/second | Validated timed responses | Invalid |
|---|---:|---:|---:|
| 1 | 402,827.99 | 6,053,894 | 0 |
| 2 | 417,212.50 | 6,270,492 | 0 |
| 3 | 413,593.88 | 6,216,493 | 0 |

Median: **413,593.88 req/s**. All three runs exceed 400,000/s.
Total timed responses checked: **18,540,879**, with zero invalid responses.
Server CPU use is about 3.99 CPU seconds/wall second. The process has 12 observed
OS threads, including runtime helpers; this is a four-worker/four-CPU result.
These are workload/host-specific measurements, not an arbitrary-application SLA.

The older callback controller was faster; the earlier pure-reactor comparison
showed about a 13% regression. Those negative results are retained in
[the earlier comparison](../2026-10-24-pure-controller-throughput/) and
[history](../../HISTORY.md). No historical measurement is relabelled as this source.
