import Std.Time

namespace FastHTTP

/-- IMF-fixdate in GMT, independent of the host's local time zone. -/
def httpDate (timestamp : Std.Time.Timestamp) : String :=
  let format : Std.Time.GenericFormat .any := .spec! "EEE, dd MMM uuuu HH:mm:ss 'GMT'"
  format.format (Std.Time.DateTime.ofTimestamp timestamp
    (Std.Time.TimeZone.ZoneRules.ofTimeZone Std.Time.TimeZone.GMT))

/-- Per-server cache: format at most once per monotonic second, including prepared
responses reused indefinitely. The cached buffer also terminates the head. -/
structure DateCache where
  private value : IO.Ref (Nat × ByteArray)

private def currentDate : IO ByteArray := do
  return ("Date: " ++ httpDate (← Std.Time.Timestamp.now) ++ "\r\n\r\n").toUTF8

def DateCache.create : IO DateCache := do
  return ⟨← IO.mkRef ((← IO.monoMsNow) / 1000, ← currentDate)⟩

def DateCache.get (cache : DateCache) : IO ByteArray := do
  let second := (← IO.monoMsNow) / 1000
  let (previous, bytes) ← cache.value.get
  if second == previous then return bytes
  let bytes ← currentDate
  cache.value.set (second, bytes)
  return bytes

end FastHTTP
