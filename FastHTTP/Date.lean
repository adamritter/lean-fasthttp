import Std.Time
import FastHTTP.DateHeader

namespace FastHTTP

/-- IMF-fixdate in GMT, independent of the host's local time zone. -/
def httpDate (timestamp : Std.Time.Timestamp) : String :=
  let format : Std.Time.GenericFormat .any := .spec! "EEE, dd MMM uuuu HH:mm:ss 'GMT'"
  format.format (Std.Time.DateTime.ofTimestamp timestamp
    (Std.Time.TimeZone.ZoneRules.ofTimeZone Std.Time.TimeZone.GMT))

/-- Per-server cache: format at most once per monotonic second, including prepared
responses reused indefinitely. The cached buffer also terminates the head. -/
structure DateCache where
  private value : IO.Ref (Nat × DateHeader)

private def currentDate : IO DateHeader := do
  let bytes := ("Date: " ++ httpDate (← Std.Time.Timestamp.now) ++ "\r\n\r\n").toUTF8
  IO.ofExcept ((DateHeader.create bytes).mapError IO.userError)

def DateCache.create : IO DateCache := do
  return ⟨← IO.mkRef ((← IO.monoMsNow) / 1000, ← currentDate)⟩

def DateCache.getChecked (cache : DateCache) : IO DateHeader := do
  let second := (← IO.monoMsNow) / 1000
  let (previous, bytes) ← cache.value.get
  if second == previous then return bytes
  let bytes ← currentDate
  cache.value.set (second, bytes)
  return bytes

/-- Compatibility view; the stored cache entry is still grammar-certified. -/
def DateCache.get (cache : DateCache) : IO ByteArray := do
  return (← cache.getChecked).bytes

end FastHTTP
