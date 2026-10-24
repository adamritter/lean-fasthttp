import FastHTTP.Protocol
import Lean.Data.Json

open Lean FastHTTP

private def unhex (text : String) : Except String ByteArray := do
  let bytes := text.toUTF8
  if bytes.size % 2 != 0 then throw "odd hex length"
  let digit (b : UInt8) : Nat := if b <= 57 then b.toNat - 48 else (lower b).toNat - 87
  let mut out := ByteArray.empty
  for i in [:bytes.size / 2] do
    let a := bytes[2*i]!
    let b := bytes[2*i+1]!
    if !hexDigit a || !hexDigit b then throw "invalid hex"
    out := out.push (UInt8.ofNat (digit a * 16 + digit b))
  return out

private def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun b =>
    let n := b.toNat
    [Char.ofNat (if n / 16 < 10 then n / 16 + 48 else n / 16 + 87),
     Char.ofNat (if n % 16 < 10 then n % 16 + 48 else n % 16 + 87)])

private def requestJSON (r : Request) : Json := Json.mkObj [
  ("method", toJson r.method), ("target", toJson r.target),
  ("authority", toJson r.authority), ("body", toJson (hex r.body)),
  ("close", toJson r.close), ("minor", toJson r.versionMinor),
  ("trailers", toJson (r.rawTrailers.map fun (k,v) => (k, hex v)))]

private structure Result where
  requests : Array Json := #[]
  rawHeaders : Array String := #[]
  continues : Nat := 0
  error : Nat := 0

private def drain (cfg : Config) (step : Protocol.Step) (out : Result) :
    Nat → Protocol.State × Result
  | 0 => (.head, { out with error := 999 })
  | fuel + 1 => match step with
    | .need state => (state, out)
    | .reject status => (.head, { out with error := status })
    | .«continue» state => drain cfg (Protocol.feed cfg state .empty)
        { out with continues := out.continues + 1 } fuel
    | .request r rest =>
      let out := { out with requests := out.requests.push (requestJSON r), rawHeaders := out.rawHeaders.push (hex r.raw) }
      -- A closing request ends the connection; pipeline bytes must not dispatch.
      if r.close then (.head, out)
      else if rest.isEmpty then (.head, out)
      else drain cfg (Protocol.feed cfg .head rest) out fuel

private def evaluate (input : Json) : Except String Json := do
  let chunks ← input.getObjValAs? (Array String) "chunks"
  let limits := (input.getObjValAs? (Array Nat) "limits").toOption.getD #[16384,1048576,1024,16384,65536]
  if limits.size != 5 then throw "five limits required"
  let cfg : Config := {
    maxHeaderBytes := limits[0]!
    maxBodyBytes := limits[1]!
    maxChunkLineBytes := limits[2]!
    maxTrailerBytes := limits[3]!
    maxChunks := limits[4]! }
  let mut state : Protocol.State := .head
  let mut out : Result := {}
  let mut closed := false
  for chunk in chunks do
    if out.error == 0 && !closed then
      let bytes ← unhex chunk
      let (next, result) := drain cfg (Protocol.feed cfg state bytes) out 100000
      state := next
      out := result
      closed := ((out.requests.back?).bind fun j => (j.getObjValAs? Bool "close").toOption).getD false
  let pending := match state with
    | .head bytes _ => if bytes.isEmpty then "idle" else "head"
    | .body .. => "body"
  return Json.mkObj [("requests", .arr out.requests), ("continues", toJson out.continues),
    ("error", toJson out.error), ("pending", toJson pending), ("raw_headers", toJson out.rawHeaders)]

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= evaluate
    match result with
    | .ok value => stdout.putStrLn value.compress
    | .error msg => throw (IO.userError msg)
