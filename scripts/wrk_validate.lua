-- Validate every timed response, in each client's Lua state. All request counts
-- must agree with wrk's independently maintained completed-response counter.
local threads = {}
local expected = string.rep("x", 1024)
validated = 0
invalid = 0

function setup(thread)
  table.insert(threads, thread)
end

function response(status, headers, body)
  validated = validated + 1
  if status ~= 200 or headers["Content-Length"] ~= "1024" or body ~= expected then
    invalid = invalid + 1
  end
end

function done(summary, latency, requests)
  local checked, bad = 0, 0
  for _, thread in ipairs(threads) do
    checked = checked + thread:get("validated")
    bad = bad + thread:get("invalid")
  end
  io.write(string.format("Validated responses: %d; invalid: %d; completed: %d\n", checked, bad, summary.requests))
end
