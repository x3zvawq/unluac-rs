-- regress_291_luau_inlined_loop_stateful_exit: O2内联loop的normal-only出口不能提前执行
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[if not]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local calls = {}

local function hit()
    table.insert(calls, "hit")
    return nil
end

local function miss()
    table.insert(calls, "miss")
    return false
end

local function any(a)
    for i = 1, #a do
        if a[i] then
            return hit()
        end
    end
    return miss()
end

local first = any({ true })
local second = any({ false })
assert(first == nil, first)
assert(second == false, second)
assert(table.concat(calls, ",") == "hit,miss", table.concat(calls, ","))
print("regress_291_luau_inlined_loop_stateful_exit", table.concat(calls, ","))
