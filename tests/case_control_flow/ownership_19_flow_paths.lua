-- Shared flow events must distinguish loop initialization, backedges and terminal reads.
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@proto=0]]
-- parallel_exit 的两个源码绑定已足够承载并行赋值与返回。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=6]] [[@dialect=luajit]]
-- Luau/JIT 的原写回保留初始化的可变身份，不能让后续编译把原加法折成常量。
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-min [[assign]] [[1]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=7]] [[@dialect=luajit]]
local function branch_exit(flag)
    local state = 10
    local result = state + 3
    if false then
        print("unreachable", state)
    end
    if flag then
        return result
    end
    state = result
    return state
end
print("branch-exit", branch_exit(false), branch_exit(true))

local function parallel_exit(flag)
    local state = 7
    local result = state + 2
    if flag then
        return state, result
    end
    state, result = result, 19
    return state, result
end
print("parallel-old", parallel_exit(true))
print("parallel-new", parallel_exit(false))

local function loops(limit, stop)
    local state = 3
    for i = 1, limit do
        local result = state + i
        repeat
            if i == stop then
                break
            end
            result = result + 2
        until true
        state = result
        if i == stop then
            break
        end
    end
    return state
end
print("loops", loops(0, 2), loops(4, 2), loops(4, 0))

local factory_calls = 0
local function factory(limit, initial)
    factory_calls = factory_calls + 1
    local i = 0
    return function()
        i = i + 1
        if i <= limit then
            return i, initial + i
        end
    end
end
local function generic(limit, stop)
    local state = 5
    for i, value in factory(limit, state) do
        local result = state + value
        if i == stop then
            return result, state
        end
        state = result
    end
    return state, state
end
print("generic-empty", generic(0, 0))
print("generic-complete", generic(3, 0))
print("generic-return", generic(3, 2))
print("factory-calls", factory_calls)

local function latch(limit)
    local state = 0
    repeat
        local result = state + 1
        state = result
    until state >= limit
    return state
end
print("latch", latch(0), latch(3))

assert(branch_exit(false) == 13 and branch_exit(true) == 13)
local parallel_first, parallel_second = parallel_exit(true)
assert(parallel_first == 7 and parallel_second == 9)
parallel_first, parallel_second = parallel_exit(false)
assert(parallel_first == 9 and parallel_second == 19)
assert(loops(0, 2) == 3 and loops(4, 2) == 8 and loops(4, 0) == 21)
local generic_first, generic_second = generic(0, 0)
assert(generic_first == 5 and generic_second == 5)
generic_first, generic_second = generic(3, 0)
assert(generic_first == 26 and generic_second == 26)
generic_first, generic_second = generic(3, 2)
assert(generic_first == 18 and generic_second == 11)
assert(latch(0) == 1 and latch(3) == 3)
assert(factory_calls == 6)
assert(branch_exit(nil) == 13 and branch_exit(0) == 13)
parallel_first, parallel_second = parallel_exit(0)
assert(parallel_first == 7 and parallel_second == 9)
parallel_first, parallel_second = parallel_exit(nil)
assert(parallel_first == 9 and parallel_second == 19)
assert(loops(-1, 0) == 3 and loops(4, 1) == 4)
assert(loops(4, 4) == 19 and loops(4, nil) == 21)
generic_first, generic_second = generic(-1, 0)
assert(generic_first == 5 and generic_second == 5)
generic_first, generic_second = generic(3, 1)
assert(generic_first == 11 and generic_second == 5)
generic_first, generic_second = generic(3, 3)
assert(generic_first == 26 and generic_second == 18)
assert(factory_calls == 9)
assert(latch(-1) == 1 and latch(1) == 1)
