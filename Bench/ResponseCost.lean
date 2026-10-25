import FastHTTP.Response

/-! Component timing only: constructor plus buffer selection, without HTTP,
routing or cancellation. Vary status to prevent loop-invariant construction. -/
@[noinline] private def make (body : ByteArray) (status : Nat) :=
  FastHTTP.Response.create body status "OK" "text/plain; charset=utf-8"
    #[("x-middleware", "ran")]

def main (args : List String) : IO Unit := do
  let count := (args[0]?.getD "1000000").toNat!
  let mode := args[1]?.getD "keep"
  let body := (String.ofList (List.replicate 1024 'x')).toUTF8
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:count] do
    let response ← IO.ofExcept ((make body (200 + i % 2)).mapError IO.userError)
    let buffers := response.buffers (mode == "close") false "\r\n".toUTF8 (mode == "legacy")
    checksum := checksum + buffers[0]!.size + buffers.size
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"mode={mode} iterations={count} nanoseconds={elapsed} checksum={checksum}"
