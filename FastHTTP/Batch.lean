import FastHTTP.Stream

namespace FastHTTP.AsyncStream.ReadyBatch

/-- The byte operation used by ready-only batching, independent of HTTP chunk
framing. Existing encodeChunk proofs provide framing for each resulting batch. -/
@[inline] def append (buffer bytes : ByteArray) : ByteArray := buffer ++ bytes

def payload (chunks : List ByteArray) (initial : ByteArray := ByteArray.empty) : ByteArray :=
  chunks.foldl append initial

end FastHTTP.AsyncStream.ReadyBatch
