# Complete parsing grammar checkpoint

The kernel checks exact, two-way grammar equivalence for the production request-head parser and optimized body decoder. `HeadGrammar` includes field semantics, routing spans, framing, connection policy and unsupported-feature rejection. `BodyWire` independently specifies successful byte transitions, complete wire prefixes, payloads and trailers. These are grammar/protocol claims; no native contract is assumed by these theorems.

Fresh generated examples and four-worker socket tests were run after rebuilding and checking the installed executable against the source manifest. See the JSON files for seeds and source/binary hashes. Remaining driver, response-construction and conditional end-to-end obligations are tracked in `FORMAL_SCOPE.md`. This checkpoint is not labelled as full HTTP/1.1 conformance.
