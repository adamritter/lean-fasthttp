# LeanUV source used by FastHTTP

`lean_uv/` is a source copy of `adamritter/lean-uv` commit
`1d116e2a8c368ca932efbf6a16a6c8ef1e548596`, retaining its license. It replaces
the existing git dependency with a local path dependency; no LeanIO dependency
is introduced. The workspace's separate `lean-uv/` checkout is untouched.

[lean_uv-streaming.patch](lean_uv-streaming.patch) records the differences:

- While a connection is waiting for a producer/handler or queued writes,
  check `SO_ERROR` before its wake callback. A paused read must not hide a
  peer reset indefinitely. This check does not consume request bytes and does
  not interpret TCP FIN as cancellation; write-half closure remains supported.
- Successful socket writes update idle activity. An active SSE heartbeat or
  download must not be closed by an idle timer based only on incoming bytes.
- Use the enclosing project's Lean 4.35 toolchain for standalone dependency
  tests as well. The upstream copy's toolchain was Lean 4.26.

The source copy includes upstream reactor contracts and tests. The native C
changes are tested, not formally verified. Existing proof statements retain
their explicit transport/runtime assumptions.
