-- regress_257_enclosing_loop_escape_fence: enclosing while 的 break 不能伪装 single-pass fence
-- unluac: expect-contains [[while]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function run(flags, limit)
    local i = 0
    while i < limit do
        if flags[1] then
            i = i + 0
        elseif flags[2] then
            if flags[3] then break end
        end
        i = i + 0
        if flags[4] then
            i = i + 0
        elseif flags[5] then
            if flags[6] then break end
        end
        i = i + 0
        i = i + 1
    end
    return i
end

assert(run({}, 2) == 2)
assert(run({false, true, true}, 2) == 0)
assert(run({false, false, false, false, true, true}, 2) == 0)
print("regress_257_enclosing_loop_escape_fence")
