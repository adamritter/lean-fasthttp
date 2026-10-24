import FastHTTP

namespace Tests

private def expectError (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"invalid certificate accepted: {label}")

private def expectOK (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => pure ()
  | .error message => throw (IO.userError s!"valid certificate rejected: {label}: {message}")

/-- Constructor regressions run at startup in both real-socket test backends. -/
def certificateChecks : IO Unit := do
  for headers in [#[("X-One", "a"), ("x-one", "b")], #[("Content-Type", "text/plain")],
      #[("DATE", "Sat, 24 Oct 2026 12:00:00 GMT")], #[("Transfer-Encoding", "chunked")],
      #[("Content-Length", "0")], #[("Bad Name", "x")], #[("X-A", "x\r\nInjected: yes")]] do
    expectError "managed, duplicate or invalid field" (FastHTTP.Response.create "payload".toUTF8 (headers := headers))
  expectOK "repeatable Set-Cookie" (FastHTTP.Response.create .empty
    (headers := #[("Set-Cookie", "a=1"), ("set-cookie", "b=2")]))
  for status in [0, 99, 100, 199, 600, 999, 1000] do
    expectError "status range" (FastHTTP.Response.create .empty status)
  for reason in ["", "OK\r\nInjected: yes", "bad\tvalue", "bad\nvalue"] do
    expectError "status reason" (FastHTTP.Response.create .empty (reason := reason))
  let next := do
    let promise ← IO.Promise.new
    promise.resolve (.ok none)
    pure promise
  for status in [100, 204, 205, 304, 600] do
    expectError "bodyless streaming status" (FastHTTP.StreamResponse.create next (status := status))
  expectError "duplicate streaming field" (FastHTTP.StreamResponse.create next
    (headers := #[("X-One", "a"), ("x-one", "b")]))
  for date in ["Date: Sat, 24 Oct 2026 12:00:00 GMT\r\n\r\n", "Date: Thu, 01 Jan 1970 00:00:00 GMT\r\n\r\n",
      "Date: Wed, 31 Dec 2025 23:59:60 GMT\r\n\r\n"] do
    expectOK "IMF-fixdate" (FastHTTP.DateHeader.create date.toUTF8)
  for date in ["Date: Sat, 24 Oct 2026 24:00:00 GMT\r\n\r\n", "Date: Sat, 00 Oct 2026 12:00:00 GMT\r\n\r\n",
      "Date: Sat, 32 Oct 2026 12:00:00 GMT\r\n\r\n", "Date: Sat, 24 Oct 2026 12:60:00 GMT\r\n\r\n",
      "Date: Sat, 24 Oct 2026 12:00:61 GMT\r\n\r\n", "Date: Sat, 24 Bad 2026 12:00:00 GMT\r\n\r\n",
      "Date: Bad, 24 Oct 2026 12:00:00 GMT\r\n\r\n", "Date: Sat, 24 Oct 026 12:00:00 GMT\r\n\r\n",
      "Date: Sat, 24 Oct 2026 12:00:00 GMT\r\nInjected: yes\r\n\r\n"] do
    expectError "malformed date" (FastHTTP.DateHeader.create date.toUTF8)

end Tests
