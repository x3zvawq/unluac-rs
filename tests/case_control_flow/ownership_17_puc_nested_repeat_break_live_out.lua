-- regress_293_puc_nested_repeat_break_live_out: nested repeat的条件写回与early break共同决定live-out
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
local function run(a)
    local out = 0
    for i = 1, 1 do
        local j = 0
        repeat
            j = j + 1
            if i == a then
                if j == 2 then
                    break
                end
                out = out + 1
            end
            out = out + i + j
        until j >= 2
    end
    return out
end

local result = run(1)
assert(result == 3, result)
assert(run(2) == 5)
assert(run(0) == 5)
assert(run(nil) == 5)
assert(run(false) == 5)
assert(run("1") == 5)
print("regress_293_puc_nested_repeat_break_live_out", result)
