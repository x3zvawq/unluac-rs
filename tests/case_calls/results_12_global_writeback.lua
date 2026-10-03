-- 固定 CALL 结果直接按原逆序写入环境，后续表写复用准备区。
-- unluac: expect-contains [[frame_result_a, frame_result_b, frame_result_c =]]
local function assign(producer, target)
    frame_result_a, frame_result_b, frame_result_c = producer()
    target.saved = producer
end

local trace, observed = {}, {}
local token, target = {}, {}
local calls = 0
local function produce()
    calls = calls + 1
    trace[#trace + 1] = "call"
    return token, nil, false, "discarded"
end

local fail_second = false
local old = getmetatable(_G)
setmetatable(_G, {
    __newindex = function(_, key, value)
        trace[#trace + 1] = key
        assert(calls > 0 and target.saved == nil)
        if key == "frame_result_b" and fail_second then
            error("stop-writeback")
        end
        observed[key] = value
    end,
})
assign(produce, target)
assert(calls == 1 and target.saved == produce)
assert(observed.frame_result_a == token and observed.frame_result_b == nil)
assert(observed.frame_result_c == false)
assert(table.concat(trace, ",") == "call,frame_result_c,frame_result_b,frame_result_a")

trace, observed = {}, {}
target.saved = nil
fail_second = true
local ok, message = pcall(assign, produce, target)
setmetatable(_G, old)
assert(not ok and string.find(message, "stop-writeback", 1, true))
assert(calls == 2 and target.saved == nil and observed.frame_result_a == nil)
assert(observed.frame_result_c == false)
assert(table.concat(trace, ",") == "call,frame_result_c,frame_result_b")
print("global-writeback", calls, table.concat(trace, ","))
