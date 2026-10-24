# Pure HTTP controller checkpoint

The actual UV backend now executes `Driver.machine` through the generic lean-uv reactor. The new controller has complete cleanup-right conservation, including pipeline continuation, deferred replies, streams, failures and closure. Conditional native transfer distinguishes issued commands from actual finalizer invocations and TCP output. `MessageGrammarProofs` establishes exact whole-request grammar equivalence, including arbitrary fragmentation and early Expect acknowledgment.

Kernel audit: 289 theorems, standard logical axioms only. Native ExecutionContract, AdapterContract and NativeContract are explicit hypotheses, not proved C/libuv facts and not HTTP correctness assumptions.

Fresh generated parser cases, UV protocol/RFC wire suites and dynamic four-worker socket tests all passed. Three 15-second loopback runs with every 1 KiB response verified measured [418304.53, 414179.64, 423538.14] requests/s, median 418304.53; 18,872,642 timed responses were checked with no invalid response. The server used four I/O workers and a four-CPU process affinity budget; runtime helper OS threads are reported separately in the raw benchmark metadata.

The pure controller is slower than the prior callback controller (previous median 479,745 requests/s), while all three new runs exceed 400,000. Both results are preserved. Full response-construction grammar, the cross-request dispatch/response invariant and liveness obligations remain tracked in FORMAL_SCOPE.md. This is a validated intermediate checkpoint, not a claim that those remaining obligations are solved.
