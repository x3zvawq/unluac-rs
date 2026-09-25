-- 共享 continue 的条件保持短路顺序；repeat 的尾条件在每条路径上仍执行一次。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]] [[@variant=O1]]
-- unluac: expect-contains [[local a, c =]] [[@debug=retained]] [[@variant=O0]]
-- unluac: expect-contains [[local a, c =]] [[@debug=retained]] [[@variant=O1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@variant=O0]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@variant=O1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=3]] [[@variant=O0]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=3]] [[@variant=O1]]
local function mark(trace, name, value)
    trace[#trace + 1] = name
    return value
end

local function run(a, c)
    local trace = {}
    local total = 0
    for _ = 1, 2 do
        repeat
            if mark(trace, "a", a) or mark(trace, "c", c) then
                continue
            end
            repeat
                total = total + 1
                total = total + 1
            until mark(trace, "inner", true)
            total = total + 1
        until mark(trace, "tail", true)
    end
    return total, table.concat(trace, ",")
end

-- 相邻但不同的退出动作不可合并，break 与 continue 的循环效果不同。
local function mixed(a, c)
    local total = 0
    for i = 1, 3 do
        if a then
            break
        end
        if c then
            continue
        end
        total = total + i
    end
    return total
end

for mode = 0, 3 do
    local a, c = mode % 2 == 1, mode >= 2
    local total, trace = run(a, c)
    assert(total == ((not a and not c) and 6 or 0))
    if a then
        assert(trace == "a,tail,a,tail")
    elseif c then
        assert(trace == "a,c,tail,a,c,tail")
    else
        assert(trace == "a,c,inner,tail,a,c,inner,tail")
    end
    assert(mixed(a, c) == ((not a and not c) and 6 or 0))
    print("shared-short-circuit-exit", mode, total, trace)
end
