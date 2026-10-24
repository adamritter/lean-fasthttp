import FastHTTP.TargetProofs

namespace FastHTTP

/-- Wire field-value octets, including obs-text but excluding CR/LF, controls and DEL. -/
def validFieldValue (text : String) : Bool :=
  text.toUTF8.data.all fun b => (b >= 32 && b != 127) || b == 9

namespace Protocol

def validOutputName (name : String) : Bool :=
  name.utf8ByteSize > 0 && name.toUTF8.data.all token

def validOutputReason (reason : String) : Bool :=
  reason.utf8ByteSize > 0 && reason.toUTF8.data.all fun b => b >= 32 && b < 127

def outputNameIs (name target : String) : Bool := equals name.toUTF8 0 name.utf8ByteSize target true

def outputFieldAllowed (managed seen : List String) (name : String) : Bool :=
  !(managed.any (outputNameIs name)) && (outputNameIs name "set-cookie" || !(seen.any (outputNameIs name)))

def OutputNameGrammar (name : String) : Prop :=
  0 < name.utf8ByteSize ∧ ∀ b ∈ name.toUTF8.data.toList, TokenOctet b

def OutputValueGrammar (value : String) : Prop :=
  ∀ b ∈ value.toUTF8.data.toList, FieldOctet b

def OutputReasonGrammar (reason : String) : Prop :=
  0 < reason.utf8ByteSize ∧ ∀ b ∈ reason.toUTF8.data.toList, 32 ≤ b.toNat ∧ b.toNat < 127

/-- Managed fields cannot be injected. Repeated fields are rejected except for
Set-Cookie; callers can combine list-valued fields before construction. -/
def OutputFieldPolicy (managed seen : List String) (name : String) : Prop :=
  (∀ field ∈ managed, ¬TextGrammar name.toUTF8 0 name.utf8ByteSize field true) ∧
  (TextGrammar name.toUTF8 0 name.utf8ByteSize "set-cookie" true ∨
    ∀ field ∈ seen, ¬TextGrammar name.toUTF8 0 name.utf8ByteSize field true)

def renderOutputField (name value : String) : String := name ++ ": " ++ value ++ "\r\n"

/-- An independently grammatical sequence of generated field lines, with exact
input order and a case-insensitive policy for managed and duplicate names. -/
inductive OutputFields (managed : List String) : List String → List (String × String) → String → Prop where
  | empty (seen : List String) : OutputFields managed seen [] ""
  | field (seen : List String) (name value : String) (fields : List (String × String)) (tail : String) :
      OutputNameGrammar name → OutputValueGrammar value → OutputFieldPolicy managed seen name →
      OutputFields managed (name :: seen) fields tail →
      OutputFields managed seen ((name, value) :: fields) (renderOutputField name value ++ tail)

def managedResponseFields : List String :=
  ["content-length", "transfer-encoding", "connection", "trailer", "upgrade", "date"]

end Protocol
end FastHTTP
