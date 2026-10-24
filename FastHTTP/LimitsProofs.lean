import FastHTTP.HeaderLimitProofs
import FastHTTP.BodyLimitProofs

namespace FastHTTP.Protocol

/-- Body-budget invariant at the application-facing protocol boundary. -/
def ProtocolBudget (cfg : Config) : State → Prop
  | .head .. => True
  | .body _ decoder .. => BodyBudget cfg decoder

def ProtocolStepBudget (cfg : Config) : Step → Prop
  | .need state | .«continue» state => ProtocolBudget cfg state
  | .request request _ => request.body.size ≤ cfg.maxBodyBytes
  | .reject _ => True

theorem bodyStep_protocolBudget (cfg : Config) (request : Request) (decoder : BodyState)
    (bytes : ByteArray) (start : Nat) (hs : BodyBudget cfg decoder) :
    ProtocolStepBudget cfg (bodyStep cfg request decoder bytes start) := by
  have budget := decodeBody_budget cfg bytes start decoder hs
  unfold bodyStep
  cases he : decodeBody cfg bytes start decoder <;> simpa [he, BodyResultBudget, ProtocolStepBudget, ProtocolBudget] using budget

theorem headStep_protocolBudget (cfg : Config) (bytes : ByteArray) (scanner : ScanState) :
    ProtocolStepBudget cfg (headStep cfg bytes scanner) := by
  unfold headStep
  split
  · trivial
  · cases he : scanner.stop with
    | none => trivial
    | some stop =>
      simp only []
      cases hp : parseHead cfg (bytes.extract 0 stop) stop with
      | error status => trivial
      | ok head =>
        have props := parseHead_budget cfg (bytes.extract 0 stop) stop head hp
        simp only []
        split
        · simp only [ProtocolStepBudget, props.2, ByteArray.size_empty]
          omega
        · have decoderBudget : BodyBudget cfg { phase := match head.framing with
              | .fixed n => .fixed n | .chunked => .sizeLine } := by
            cases hf : head.framing with
            | fixed n => simpa [BodyBudget] using props.1 n hf
            | chunked => simp [BodyBudget]
          split
          · exact decoderBudget
          · exact bodyStep_protocolBudget cfg head.request _ bytes stop decoderBudget

/-- Every real feed operation preserves the configured body budget. This links
Content-Length validation, chunk-size validation, all decoder phases and the
Request delivered to the application, for all possible byte inputs. -/
theorem feed_protocolBudget (cfg : Config) (state : State) (input : ByteArray)
    (hs : ProtocolBudget cfg state) : ProtocolStepBudget cfg (feed cfg state input) := by
  cases state with
  | head pending scanner => exact headStep_protocolBudget cfg _ _
  | body request decoder pending start => exact bodyStep_protocolBudget cfg request decoder _ start hs

/-- No request emitted by a budget-preserving continuation can exceed the limit.
Initial head states satisfy the invariant; feed_protocolBudget preserves it
through every need/100-continue continuation and pipeline restart. -/
theorem feed_request_body_bound (cfg : Config) (state : State) (input : ByteArray)
    (request : Request) (rest : ByteArray) (hs : ProtocolBudget cfg state)
    (h : feed cfg state input = .request request rest) : request.body.size ≤ cfg.maxBodyBytes := by
  have bound := feed_protocolBudget cfg state input hs
  simpa [h, ProtocolStepBudget] using bound

end FastHTTP.Protocol
