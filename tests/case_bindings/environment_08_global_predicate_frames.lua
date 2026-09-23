-- 全局谓词读取和低槽选择写回之间不保留机械 local，后继 CALL/CONCAT 共用原准备区。
-- unluac: expect-count [[FRAME_MARKER == "hit"]] [[2]]
-- unluac: expect-count [[echo(chosen) == "value:" .. chosen]] [[2]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-contains [[local chosen = "seed"]] [[@debug=retained]]
-- unluac: expect-contains [[if reads == 1 then]] [[@debug=retained]]
-- unluac: expect-contains [[chosen = FRAME_MARKER == "hit" and "three" or "four"]] [[@debug=retained]]
local events = {}
local reads = 0
local function echo(value)
    events[#events + 1] = "echo:" .. value
    return "value:" .. value
end

local function run()
    local chosen = "seed"
    if FRAME_MARKER == "hit" then
        chosen = "one"
    else
        chosen = "two"
    end
    assert(echo(chosen) == "value:" .. chosen)
    chosen = FRAME_MARKER == "hit" and "three" or "four"
    assert(echo(chosen) == "value:" .. chosen)
    return chosen
end

local previous = getmetatable(_G)
setmetatable(_G, {
    __index = function(_, key)
        assert(key == "FRAME_MARKER")
        reads = reads + 1
        events[#events + 1] = "read:" .. reads
        if reads == 1 then
            return "hit"
        end
        return "miss"
    end,
})
local result = run()
setmetatable(_G, previous)
assert(result == "four" and reads == 2)
assert(table.concat(events, ",") == "read:1,echo:one,read:2,echo:four")
print("environment_08_global_predicate_frames", table.concat(events, ","))
