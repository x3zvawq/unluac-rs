-- regress_289_luau_closure_creation_identity: O2的DUPCLOSURE与NEWCLOSURE不能按child proto混同
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r0_9 = r0_12]]
local function shared_make()
    return function(value)
        return value + 1
    end
end

local shared_first = shared_make()
local shared_second = shared_make()

local function fresh_make(offset)
    return function(value)
        return value + offset
    end
end

local fresh_first = fresh_make(1)
local fresh_second = fresh_make(1)
assert(shared_first == shared_second and fresh_first ~= fresh_second)
assert(shared_first(10) == 11 and shared_second(20) == 21)
assert(fresh_first(10) == 11 and fresh_second(20) == 21)

local loop_first
for index = 1, 2 do
    local current = function(value)
        return value + 2
    end
    if loop_first == nil then
        loop_first = current
    else
        assert(loop_first == current and current(20) == 22)
        print("regress_289_loop_shared", index, loop_first == current, current(20))
    end
end

print(
    "regress_289_luau_closure_creation_identity",
    shared_first == shared_second,
    shared_first(10),
    shared_second(20),
    fresh_first == fresh_second,
    fresh_first(10),
    fresh_second(20)
)
