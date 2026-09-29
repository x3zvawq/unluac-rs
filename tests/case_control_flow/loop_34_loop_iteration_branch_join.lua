-- regress_488_loop_iteration_branch_join: a next-iteration postdom is not this iteration's branch join
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-min [[break]] [[1]]
local function run(a, b, c)
    local x = 0
    repeat
        if a then
            repeat
                x = x + 1
            until b
            if c then
                break
            end
        end
        while not b do
            x = x + 1
        end
    until false
    return x
end

-- Only all-truthy combinations return normally; false branches are observed by the hook below.
assert(run(true, true, true) == 1)
assert(run(1, "ready", {}) == 1)
assert(run(0, 0, 0) == 1)
assert(run("", "", "") == 1)
print("regress_488_loop_iteration_branch_join", "closed")

-- PUC/JIT 的指令 hook 有界观察其余布尔组合，不比较具体指令计数。
-- Luau 没有该 API，仍执行上面的终止路径；结构断言覆盖完整循环体。
if debug and debug.sethook then
    if jit then
        jit.off(run, true)
    end
    local stop = {}
    local function interrupt_loop()
        debug.sethook()
        error(stop)
    end
    local function check(a, b, c)
        debug.sethook(interrupt_loop, "", 1000)
        local ok, failure = pcall(run, a, b, c)
        debug.sethook()
        assert(not ok)
        assert(failure == stop)
    end
    check(false, false, false)
    check(false, false, true)
    check(false, true, false)
    check(false, true, true)
    check(true, false, false)
    check(true, false, true)
    check(true, true, false)
    print("observed_nonterminal_paths", 7)
end

-- 调试身份 x 在两层循环及出口保持同一绑定；观察器没有循环或额外状态写。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[assign]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=3]] [[@dialect=luau]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=1]] [[@dialect=luau]]
