import FastHTTP.ResponseSyntaxProofs

namespace FastHTTP

/-- Runtime validation returns a proof-carrying field block. The certificate is
erased by Lean; arbitrary strings cannot be promoted to checked fields. -/
def checkedResponseFields (managed seen : List String) (fields : List (String × String)) :
    Except String { wire : String // Protocol.OutputFields managed seen fields wire } :=
  match fields with
  | [] => .ok ⟨"", .empty seen⟩
  | (name, value) :: fields =>
    if hn : Protocol.validOutputName name then
      if hv : validFieldValue value then
        if hp : Protocol.outputFieldAllowed managed seen name then
          match checkedResponseFields managed (name :: seen) fields with
          | .error reason => .error reason
          | .ok tail => .ok ⟨Protocol.renderOutputField name value ++ tail.val,
              .field seen name value fields tail.val ((Protocol.validOutputName_iff name).mp hn)
                ((Protocol.validFieldValue_iff value).mp hv)
                ((Protocol.outputFieldAllowed_iff managed seen name).mp hp) tail.property⟩
        else .error "duplicate or managed response header"
      else .error "invalid response header value"
    else .error "invalid response header name"

def responseFields (headers : Array (String × String)) : Except String String :=
  (checkedResponseFields Protocol.managedResponseFields [] headers.toList).map Subtype.val

end FastHTTP
