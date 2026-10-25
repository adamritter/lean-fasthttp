# Action and streaming publication checkpoint

Merged the latest remote proof work with lazy Action scopes, pending completion
ownership, streaming/SSE, and the response-byte scan optimization. The input,
output and progress invariants now include waiting and cancel finalizers.

A clean build, strict 378-theorem/four-factory audit, pending lifecycle tests,
artifact-staleness regression, both transport protocol/RFC suites, generated
wire cases, UV integration and the vendored UV contract audit passed.
Source and binary hashes are recorded in verification.json. Build metadata's
Git parent predates this commit; the complete source hashes identify the tested
uncommitted publishing tree. No new throughput claim is made for this tree.

The optional integration and original throughput evidence are published in
https://github.com/adamritter/leanio-fasthttp .
