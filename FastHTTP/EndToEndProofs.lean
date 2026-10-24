import FastHTTP.DriverInputProofs
import FastHTTP.DriverOutputProofs
import FastHTTP.DriverProgressProofs
import FastHTTP.LimitsProofs

/-! The complete conditional theorem for the supported HTTP/1.1 origin-server
wire/framing model. Native assumptions are parameters, never axioms. The parser,
input provenance, response grammar/order, limits and resource accounting are
proved here; conditional progress is `driver_eventual_reply`.

Application representation/metadata semantics and clock truth are outside this
wire model. The model does not implement TLS, CONNECT tunnels or upgrades. -/
namespace FastHTTP.Protocol

/-- The same actual input cannot have two different first-request meanings or
pipeline boundaries in the supported grammar. -/
theorem request_wire_deterministic (cfg : Config) (wire : ByteArray)
    (first second : Request) (left right : ByteArray)
    (a : RequestWire cfg wire first left) (b : RequestWire cfg wire second right) :
    first = second ∧ left = right := by
  have pa := (feed_request_grammar_iff cfg wire first left).mpr a
  have pb := (feed_request_grammar_iff cfg wire second right).mpr b
  rw [pa] at pb
  exact Step.request.inj pb

/-- Even an Expect continuation's final application-facing body obeys the
configured byte limit. This uses the production feed invariant in both phases. -/
theorem request_wire_body_bound (cfg : Config) (wire : ByteArray) (request : Request) (rest : ByteArray)
    (grammar : RequestWire cfg wire request rest) : request.body.size ≤ cfg.maxBodyBytes := by
  have parsed := (feed_request_grammar_iff cfg wire request rest).mpr grammar
  have budget := feed_protocolBudget cfg .head wire trivial
  cases step : feed cfg .head wire with
  | need state => simp [step, acknowledge] at parsed
  | reject status => simp [step, acknowledge] at parsed
  | request current suffix =>
    simp only [step, acknowledge, Step.request.injEq] at parsed
    obtain ⟨rfl, rfl⟩ := parsed
    simpa only [step, ProtocolStepBudget] using budget
  | «continue» state =>
    simp only [step, acknowledge] at parsed
    have saved : ProtocolBudget cfg state := by simpa only [step, ProtocolStepBudget] using budget
    exact feed_request_body_bound cfg state .empty request rest saved parsed

/-- Once a complete message is present, dispatch is immediate or waits only
for the single 100-continue write acknowledgment. This is a real controller
transition, not merely existence of a parser result. -/
theorem complete_request_dispatch (cfg : Config) (step : Step) (request : Request) (rest : ByteArray)
    (complete : acknowledge cfg step = .request request rest) :
    Driver.accept step = (.handling request rest, .perform (.handle request)) ∨
      ∃ parser, Driver.accept step = (.continuing parser, .write #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]) ∧
        Driver.step cfg (.continuing parser) .written = (.handling request rest, .perform (.handle request)) := by
  cases step with
  | need parser => contradiction
  | reject status => contradiction
  | request current suffix =>
    simp only [acknowledge, Step.request.injEq] at complete
    obtain ⟨rfl, rfl⟩ := complete
    exact Or.inl rfl
  | «continue» parser =>
    change feed cfg parser .empty = .request request rest at complete
    exact Or.inr ⟨parser, rfl, by simp only [Driver.step, complete, Driver.accept]⟩

/-- Final reception cannot strand a complete grammatical request in a read state.
The wire witness is the accumulated real input window plus this received fragment. -/
theorem received_request_dispatch (cfg : Config) (wire bytes : ByteArray) (parser : State)
    (request : Request) (rest : ByteArray) (reading : InputState cfg wire (.reading parser))
    (grammar : RequestWire cfg (wire ++ bytes) request rest) :
    Driver.step cfg (.reading parser) (.data bytes) = (.handling request rest, .perform (.handle request)) ∨
      ∃ continuation,
        Driver.step cfg (.reading parser) (.data bytes) =
          (.continuing continuation, .write #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]) ∧
        Driver.step cfg (.continuing continuation) .written = (.handling request rest, .perform (.handle request)) := by
  have complete := (feed_request_grammar_iff cfg (wire ++ bytes) request rest).mpr grammar
  rw [feed_acknowledged_fragmentation, reading.2] at complete
  exact complete_request_dispatch cfg (feed cfg parser bytes) request rest complete

/-- The claims about one actual finite native observation. `OutputPair` is the
independent response-wire grammar plus the outstanding protocol phase at every
prefix; `InputTrace` is the receive/consume ledger with exact grammatical suffixes.
Neither property appears in any of the native assumptions. -/
structure HTTP11RunCorrect (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work) : Prop where
  receiveLedger : ∃ pending, InputState cfg pending final ∧ InputTrace cfg .empty events commands pending
  requestsFromNetwork : ∀ request, .perform (.handle request) ∈ commands → InputSegment cfg native.networkInput request
  requestBodyBound : ∀ request, .perform (.handle request) ∈ commands → request.body.size ≤ cfg.maxBodyBytes
  responseOrder : ∀ before after, events = before ++ after →
    OutputPair ((Driver.machine cfg).replay .reading before).1
      (((Driver.machine cfg).replay .reading before).2.getLastD .idle)
  orderedOutput : LeanUV.TCP.Contract.Prefix native.transportOutput (LeanUV.TCP.Machine.commandBytes commands)
  acknowledgedOutput : ∀ before after, events = before ++ .written :: after →
    (∀ event ∈ before, event ≠ .failed) →
    LeanUV.TCP.Contract.Prefix (LeanUV.TCP.Machine.commandBytes (commands.take before.length)) native.transportOutput
  gracefulOutput : native.closeReason = some .graceful → native.transportOutput = LeanUV.TCP.Machine.commandBytes commands
  actualCleanup : (invoked.map driverFinalizerWeight).sum + driverOwned final = driverAcquiredTrace cfg .reading events

/-- END-TO-END SAFETY. Under the explicit generic compiler/runtime, adapter,
transport and write-completion contracts, the deployed FastHTTP.UV controller
satisfies the complete supported HTTP/1.1 wire/framing model for every finite
observation, arbitrary input fragmentation and application replies. This includes
partial/error traces; successful graceful close additionally gives exact output.

The hypotheses contain no HTTP correctness claim. Response certificates are
checked by Lean; application code cannot construct uncertified wire buffers. -/
theorem http11_end_to_end (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked)
    (transport : LeanUV.TCP.Contract.NativeContract native)
    (completion : LeanUV.TCP.Machine.CompletionContract events commands native) :
    HTTP11RunCorrect cfg events final commands native invoked := by
  refine ⟨driver_native_input_trace cfg events final commands execution,
    driver_native_input_origin cfg events final commands native invoked execution adapter transport,
    ?_, driver_native_output_order cfg events final commands execution,
    LeanUV.TCP.Machine.adapter_output_prefix events commands native invoked adapter transport,
    completion.acknowledged,
    LeanUV.TCP.Machine.adapter_graceful_output events commands native invoked adapter transport,
    driver_actual_cleanup cfg events final commands native invoked execution adapter⟩
  intro request member
  obtain ⟨rest, wire, grammar⟩ := driver_native_requests_valid cfg events final commands execution request member
  exact request_wire_body_bound cfg wire request rest grammar

end FastHTTP.Protocol
