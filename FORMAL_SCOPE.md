# Formal scope and remaining obligations

The checked statements are about the executable Lean protocol functions. The
kernel checks every proof; the audit rejects missing theorem entries, `sorryAx`
and any axiom beyond `propext`, `Classical.choice` and `Quot.sound`. There is no
`native_decide`, custom axiom or unchecked implementation override in these proofs.

## Established properties

| Function / module | Quantification and guarantee |
|---|---|
| `scanFeedFast_reference` in `ScannerProofs` | Every byte buffer; the optimized scanner equals an independent literal CRLFCRLF suffix specification, stopping at the first delimiter or the configured limit. |
| `scanFeedFast_append` / `scanFeed_fragments` | Every scanner state and every pair/list of byte buffers; the result is unchanged by fragmentation. |
| `bodyFastLoop_eq_bodyLoop` in `BodyFastProofs` | Every Config, ByteArray, cursor and BodyScan; the actual bulk-copy loop equals the terminating byte-machine loop. All payload branches are covered, including fixed and chunked bodies. |
| `decodeBody_fragmentation` | Every Config, initial BodyState and pair of byte arrays. A suspended decoder restarted on the second array equals concatenated decoding. The equality includes payload, raw trailers, error status and the first stop offset, with the explicit relative-cursor adjustment. Repeated application covers arbitrarily many fragments. |
| `decodeBody_fixed_exact` | Every binary payload, saved body prefix and arbitrary following suffix; the decoded bytes are exactly prefix ++ payload and the stop offset is exactly the declared payload length. |
| `decodeBody_pipeline_suffix` | Any completed public-decoder result and any appended byte suffix; the body, trailers and stop offset remain unchanged. |
| `decodeBody_done_bounds` / `decodeBody_partition` | For any valid starting cursor, a successful stop stays inside the input; the consumed wire prefix and untouched suffix partition that input. |
| `bodyByte_live` / `bodyList_more` | Every suspended state has a nonempty fixed remainder or a chunk phase; suspension consumes the entire supplied fragment. This is used in the public decoder composition proof. |
| `feed_fragmentation` / `feed_fragments` in `FeedProofs` | The complete production `feed` function, every bounded state and every pair/finite list of byte buffers. Equality includes the complete Request (raw header bytes, all metadata, binary body, raw trailers), rejection status, Expect continuation and untouched pipeline bytes. `appendStep` explicitly buffers bytes arriving while a 100-continue action awaits acknowledgment. |
| `feed_bound` / `feed_body_no_continue` | Every emitted continuation preserves the cursor invariants; a body continuation cannot emit another 100-continue action. |
| `parseRequestLine_iff` / `parseFieldLine_iff` in `LexicalProofs` | Soundness and completeness against independent wire-envelope grammars: nonempty tchar method and field name, exact SP/colon/CRLF positions, supported HTTP/1.x version digits, ASCII target envelope, all field-value octets including obs-text, exact returned spans and target limit. URI and field-specific semantics are separate obligations. |
| `parseHead_envelope` in `HeaderProofs` | Every accepted production request head has that grammatical request line and a complete inductive sequence of valid field lines ending at the empty CRLF, with the exact raw bytes and metadata returned to the application. |
| `decimal_iff` in `NumericProofs` | Every byte array, interval, limit and result; the production Content-Length parser succeeds iff the interval is nonempty and in bounds, contains only RFC ASCII DIGIT octets, and its positional decimal value equals the result without exceeding the limit. |
| `validPathQuery_iff` / `uriComponent_iff` in `SyntaxProofs` | Every wire interval and literal alphabet; acceptance is equivalent to an independent inductive grammar whose productions consume one literal or exactly percent + two ASCII HEXDIG octets. The path/query instantiation uses the RFC 3986 pchar, slash and question-mark alphabet. |
| `chooseFraming`, `takeCount`, `takeBody` | Conflicting CL/TE rejection; exact declared fixed lengths; bounded byte slices, conservation, partition and fixed-body fragmentation. |
| `wireBody`, `responseLength` | HEAD/204/304 body suppression and ordinary prepared-body length correspondence; 204 omits Content-Length. |

`bodyLoop`/`bodyFold` specify the byte-by-byte execution of `bodyByte`.
`bodyFastLoop` is the implementation used by `decodeBody`, and `Protocol.feed`
calls this decoder. The proof does not rely on generated test cases. It also
does not assert that every branch of `bodyByte` has independently been proved
equivalent to RFC ABNF: that distinction matters for the lexical helpers below.

## Not yet a full HTTP/1.1 conformance proof

The following obligations are not established by these theorems:

* The remaining URI authority/IPv6 grammar and field-specific Host, Connection,
  Expect and Transfer-Encoding semantics against the RFCs. The request-line
  envelope, field-line envelope, complete accepted header-block structure and
  URI atom grammar now have independent formal specifications and proofs.
* Hex parsing and chunk extension/trailer lexical correspondence with
  that grammar, and correctness of decimal/hex wire serialization.
* Application dispatch and the IO acknowledgment of actions. Pure head-plus-body
  feed composition, including all metadata and Expect buffering, is established.
* Response/stream ordering, cancellation, cleanup and liveness of the actual IO
  interpreter, and the C/libuv socket lifetime implementation.

These areas have independent generated and real-socket regressions, including
all byte values in field values, independently generated IPv6 addresses, malformed
framing, every split of representative messages, dynamic four-worker pipelines,
deferred promises, slow readers, half-close and producer failure. Tests are
empirical evidence, not formal proofs of the remaining obligations. Therefore
**the repository must not be described as a fully proved HTTP/1.1 implementation**.

The trust boundary includes the Lean kernel, compiler and runtime, the native
implementations of Lean's primitive data structures, the C FFI, libuv and the OS.
The C FFI's sanitizer evidence is stored in the pinned lean-uv repository; its
prebuilt Lean runtime is not sanitizer-instrumented. No TLS correctness claim is
made. CONNECT/upgrade are unsupported application/transport features; their
absence alone is not the definition of an HTTP parsing error.
