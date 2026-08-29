-- regress_337: fixed call results may be nil, so raw SETLIST must not be split into SETTABLE.

local calls = 0
local function maybe_nil()
    calls = calls + 1
    return nil
end

local values = { "head", (maybe_nil()), "tail" }
print("regress_337#nil-shape", calls, #values, values[1], values[2], values[3])
