-- regress_256_nested_loop_header_arm: branch arm 直接进入唯一 nested-loop header
-- unluac: expect-contains [[while]]
-- unluac: expect-contains [[if]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_0]]

local function run(outer, inner, stop)
    while outer do
        if inner then
            while inner do
                if stop then return "stopped" end
                inner = false
            end
        end
        outer = false
    end
    return "done"
end

assert(run(true, true, true) == "stopped")
assert(run(true, true, false) == "done")
assert(run(true, false, false) == "done")
print("regress_256_nested_loop_header_arm")
