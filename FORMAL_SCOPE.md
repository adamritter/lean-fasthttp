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
| `decimal_wire_roundtrip` / `encodeChunk_wire` in `WireProofs` | Every natural length and every binary payload. The actual decimal formatter round-trips through the production bounded parser; the actual chunk encoder emits hexadecimal length + CRLF, the unchanged payload and CRLF. UTF-8 ASCII correspondence and positional value are proved for all bases 2..16, without a machine-word bound. |
| `streamStep_*` / `streamTrace_*` / `streamCommands_head` in `StreamMachineProofs` | Both actual transports execute `Protocol.streamStep`. Every finite callback-event trace conserves a single cleanup right; cleanup occurs at most once and exactly once after ownership ends. Producer pulls require a write-completion event; body writes require a pending producer result; HEAD never pulls or emits body chunks; HTTP/1.0 EOF and HTTP/1.1 final-chunk ordering are distinguished. |
| `feed_protocolBudget` / `feed_request_body_bound` in `LimitsProofs` | End-to-end body-limit preservation for the production feed function. Content-Length interpretation, framing selection, hexadecimal chunk sizes, all byte-machine phases and every bulk path are covered. Every need/continue preserves the budget and every delivered Request.body fits maxBodyBytes. Initial head states satisfy the invariant. |
| `hexadecimal_iff` / `chunkSize_numeral` in `HexProofs` | The production bounded hexadecimal parser accepts exactly nonempty HEXDIG sequences with the stated positional value within the limit. Every accepted chunk-size line has that numeral and an accepted extension suffix; the latter is now connected to the complete extension grammar by `chunkSize_grammar`. |
| `chunkExtensions_iff` / `chunkSize_grammar` in `ChunkGrammarProofs` | The complete production chunk-extension parser accepts exactly the independently specified RFC BWS/semicolon/token/optional-value grammar. Both directions include all whitespace positions and arbitrary quoted values. No maximal-token assumption is added to the specification. Chunk-size acceptance combines this with the exact bounded hexadecimal numeral. |
| `trailer_iff` / `trimSpan_exact` in `TrailerProofs` | Exact equivalence of the production trailer parser to the independent field-line envelope, the explicit forbidden-name policy, and the original binary value with only outer OWS removed. Every interior octet is preserved, including obs-text and all-whitespace values. |
| `quotedEnd_iff` in `QuotedProofs` | Soundness/completeness against an independent RFC 9110 quoted-string grammar, including every escaped octet, obs-text, rejected controls/DEL, missing terminators and the exact closing cursor. The same production function is called for chunk extensions and Transfer-Encoding parameters. |
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
* An independent whole-message chunked-body ABNF equivalence. The complete
  chunk-extension grammar, trailer field grammar, quoted strings, decimal and
  hexadecimal numerals and wire serialization now have proofs; the body automaton
  has bulk-loop refinement, fragmentation and budget proofs. These are not yet a
  single whole-message RFC grammar equivalence theorem.
* Application dispatch and the IO acknowledgment of actions. Pure head-plus-body
  feed composition, including all metadata and Expect buffering, is established.
* End-to-end IO refinement and liveness, cancellation of application-owned
  producers, and the C/libuv socket lifetime implementation. Stream control and
  cleanup decisions are now proved and executed by both adapters; callback
  delivery, IO.Ref behavior and native writes remain inside the trust boundary.

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
