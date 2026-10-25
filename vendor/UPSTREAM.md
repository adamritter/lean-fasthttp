# LeanUV source used by FastHTTP

`lean_uv/` is a source copy of `adamritter/lean-uv` commit
`1d116e2a8c368ca932efbf6a16a6c8ef1e548596`, retaining its license. It replaces
the existing git dependency with a local path dependency; no LeanIO dependency
is introduced. The workspace's separate `lean-uv/` checkout is untouched.

[lean_uv-streaming.patch](lean_uv-streaming.patch) records the differences:

- Replace 10 ms completion polling with a deduplicated `uv_async_t` queue and
  thread-safe `Socket.notify`. Refcounted wake hubs outlive retained sockets.
- Require one-shot completion subscription in `Machine.callbacks`; fuel yields
  explicitly notify. Adapt the native fixtures and add late-notification stress.
- Watch ERR/HUP via a separate epoll descriptor while a connection is waiting.
  Paused reads cannot hide peer resets. No request bytes are consumed, and TCP
  write-half closure remains supported.
- Successful socket writes update idle activity. An active SSE heartbeat or
  download must not be closed by an idle timer based only on incoming bytes.
- Use the enclosing project's Lean 4.35 toolchain for standalone dependency
  tests as well. The upstream copy's toolchain was Lean 4.26.

The source copy includes upstream reactor contracts and tests. The native C
changes are tested, not formally verified. Existing proof statements retain
their explicit transport/runtime assumptions.
