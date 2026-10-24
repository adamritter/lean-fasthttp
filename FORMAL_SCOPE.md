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
| `feed_request_grammar_iff` / `feed_live_fragments_grammar_iff` in `MessageGrammarProofs` | Exact complete RequestWire equivalence for the public parser, including independent first-delimiter, head and body grammars, all request fields and untouched pipeline bytes. Arbitrary fragmentation and acknowledgment of Expect after each fragment produce the same complete result. |
| `prepared_buffers_grammar` / `streaming_buffers_grammar` / `encoded_chunk_grammar` in `ResponseProofs` | Every prepared/streaming response, Date header, connection/version/HEAD choice and binary chunk. Complete wire productions include exact three-digit status, decimal/hexadecimal byte counts, field grammar, managed/duplicate field policy, Date grammar, body suppression and the final empty line. Response objects carry erased grammar certificates; their factory definitions are separately axiom-audited. |
| `driver_native_requests_valid` in `DriverRequestProofs` | Every handler command in an arbitrary actual controller replay has a complete RequestWire witness. Linking that witness to the actual receive ledger is still a separate obligation below. |
| `driver_step_resource` / `driver_replay_resource` in `DriverProofs` | Every transition and finite trace of the actual complete HTTP reactor conserves acquired stream cleanup rights. Error, close, malformed event ordering, deferred responses, stream completion and pipeline continuation are covered. |
| `driver_actual_cleanup` / `driver_actual_graceful_output` in `DriverNativeProofs` | Conditional native transfer under the visible lean-uv ExecutionContract, AdapterContract and NativeContract. Actual cleanup invocations conserve acquired rights; TCP output is an ordered prefix of selected controller output, or the exact selected output after successful graceful close. Complete response serialization is proved separately in ResponseProofs; the cross-request composition remains below. |
| `parseHead_grammar_iff` in `HeadGrammarProofs` | Exact equivalence of the complete production head parser and independently specified request-line, all four target forms, complete ordered header semantics, framing and supported-feature policy. Includes every returned routing span, HTTP version, connection/HEAD/Expect flag and duplicate-field rejection. |
| `parseField_grammar_iff` / `parseHeaders_grammar_iff` | Each grammatical field updates exactly the accumulated Content-Length, Transfer-Encoding, Host, Expect and Connection state; both directions cover the complete ordered field block and mandatory Host policy. |
| `decodeBody_grammar_iff` / `decodeChunked_grammar_iff` in `BodyGrammarProofs` | The actual optimized decoder succeeds iff the input has an independently grammatical body prefix. Exact decoded payload, raw trailers, stopping cursor and untouched suffix are included. `BodyWire` is an inductive operational wire grammar; its byte productions use independent numeral, extension and trailer grammars, not calls to the body parser. |
| `parseHead_envelope` in `HeaderProofs` | Every accepted production request head has that grammatical request line and a complete inductive sequence of valid field lines ending at the empty CRLF, with the exact raw bytes and metadata returned to the application. |
| `decimal_wire_roundtrip` / `encodeChunk_wire` in `WireProofs` | Every natural length and every binary payload. The actual decimal formatter round-trips through the production bounded parser; the actual chunk encoder emits hexadecimal length + CRLF, the unchanged payload and CRLF. UTF-8 ASCII correspondence and positional value are proved for all bases 2..16, without a machine-word bound. |
| `streamStep_*` / `streamTrace_*` / `streamCommands_head` in `StreamMachineProofs` | Both actual transports execute `Protocol.streamStep`. Every finite callback-event trace conserves a single cleanup right; cleanup occurs at most once and exactly once after ownership ends. Producer pulls require a write-completion event; body writes require a pending producer result; HEAD never pulls or emits body chunks; HTTP/1.0 EOF and HTTP/1.1 final-chunk ordering are distinguished. |
| `feed_protocolBudget` / `feed_request_body_bound` in `LimitsProofs` | End-to-end body-limit preservation for the production feed function. Content-Length interpretation, framing selection, hexadecimal chunk sizes, all byte-machine phases and every bulk path are covered. Every need/continue preserves the budget and every delivered Request.body fits maxBodyBytes. Initial head states satisfy the invariant. |
| `hexadecimal_iff` / `chunkSize_numeral` in `HexProofs` | The production bounded hexadecimal parser accepts exactly nonempty HEXDIG sequences with the stated positional value within the limit. Every accepted chunk-size line has that numeral and an accepted extension suffix; the latter is now connected to the complete extension grammar by `chunkSize_grammar`. |
| `chunkExtensions_iff` / `chunkSize_grammar` in `ChunkGrammarProofs` | The complete production chunk-extension parser accepts exactly the independently specified RFC BWS/semicolon/token/optional-value grammar. Both directions include all whitespace positions and arbitrary quoted values. No maximal-token assumption is added to the specification. Chunk-size acceptance combines this with the exact bounded hexadecimal numeral. |
| `trailer_iff` / `trimSpan_exact` in `TrailerProofs` | Exact equivalence of the production trailer parser to the independent field-line envelope, the explicit forbidden-name policy, and the original binary value with only outer OWS removed. Every interior octet is preserved, including obs-text and all-whitespace values. |
| `quotedEnd_iff` in `QuotedProofs` | Soundness/completeness against an independent RFC 9110 quoted-string grammar, including every escaped octet, obs-text, rejected controls/DEL, missing terminators and the exact closing cursor. The same production function is called for chunk extensions and Transfer-Encoding parameters. |
| `decimal_iff` in `NumericProofs` | Every byte array, interval, limit and result; the production Content-Length parser succeeds iff the interval is nonempty and in bounds, contains only RFC ASCII DIGIT octets, and its positional decimal value equals the result without exceeding the limit. |
| `connectionOptions_iff` / `transferCodings_iff` in `FieldsProofs` | Exact full comma-list grammars with ignored empty members, accumulated close/chunked/unsupported flags, transfer parameters and quoted strings. Chunked is unique, final and parameter-free, including a previous field's chunked flag. Every production loop is total. |
| `validAuthority_iff` / `validIPvFuture_iff` in `AuthorityProofs` | Soundness and completeness of the complete Host/authority grammar: reg-name percent atoms, bracketed IPv6/IPvFuture, optional decimal port, and CONNECT nonempty host/port requirements. All interval scans terminate. |
| `parseTarget_iff` in `TargetProofs` | Exact production request-target equivalence for all four forms, scheme syntax, userinfo policy, HTTP(S) authority precedence, path spans and unsupported-scheme metadata. `equals_iff` proves the underlying byte-text comparison. |
| `validIPv4_iff` / `validIPv6_iff` / `utf8IPv6_iff` in `IPv6Proofs` | Exact equivalence to the RFC decimal-octet and counted IPv6 group grammar: eight 16-bit pieces, one optional compression eliding at least one piece, and an IPv4 tail only in the final two pieces. Decimal octets exclude leading zeros and values above 255. Malformed UTF-8 is rejected without panic. Group traversal uses structural list recursion rather than repeated indexing. |
| `validPathQuery_iff` / `uriComponent_iff` in `SyntaxProofs` | Every wire interval and literal alphabet; acceptance is equivalent to an independent inductive grammar whose productions consume one literal or exactly percent + two ASCII HEXDIG octets. The path/query instantiation uses the RFC 3986 pchar, slash and question-mark alphabet. |
| `chooseFraming`, `takeCount`, `takeBody` | Conflicting CL/TE rejection; exact declared fixed lengths; bounded byte slices, conservation, partition and fixed-body fragmentation. |
| `wireBody`, `responseLength` | HEAD/204/304 body suppression and ordinary prepared-body length correspondence; 204 omits Content-Length. |

`bodyFastLoop` is the implementation used by `decodeBody`, and `Protocol.feed`
calls this decoder. `BodyGrammarProofs` connects every successful byte transition
and the entire optimized fold to `BodyWire`, including limits and trailers.
The proof does not rely on generated test cases. `BodyWire` is an operational
wire grammar, not a transcription of RFC ABNF into a separate grammar language.

## Not yet a full HTTP/1.1 conformance proof

The following obligations are not established by these theorems:

* The actual-input provenance and full cross-request dispatch/response invariant.
  Complete parser grammar equivalence, response wire grammar, grammatical
  handler dispatch and cleanup conservation are proved. Native read/write/finalizer
  refinement is an explicit generic contract, with conditional transfer proofs.
* Liveness and the external application's producer/cancellation semantics.
  Native C/libuv socket lifetimes, callback delivery and IO.Ref execution are
  explicit trusted assumptions, not claimed as C implementation proofs.

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
