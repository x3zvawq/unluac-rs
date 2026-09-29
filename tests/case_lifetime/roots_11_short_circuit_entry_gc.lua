-- 入口 TEST 后的各 successor 都先覆盖同槽 callee：不能额外保活第一次调用结果。
-- unluac: expect-contains [[("a") and]]
-- LuaJIT 的子 proto 顺序不同；选择各方言实际的 choose/keep_entry。
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-max [[local-binding]] [[10]]
-- unluac: expect-ast-count [[function]] [[4]]
local function choose(step)
    return (step("a") and (step("b") or step("c")) and step("d")) or step("e")
end

-- 独立源码 local 处于后续 call frame 下方，不能套用短路入口的覆盖证书。
local function keep_entry(step)
    local saved = step("a")
    return (saved and (step("b") or step("c")) and step("d")) or step("e")
end

local function check(run, keep, false_steps, expected, expected_type)
    local weak = setmetatable({}, {__mode = "v"})
    local log = {}
    local function step(name)
        collectgarbage("collect")
        collectgarbage("collect")
        assert((weak.a ~= nil) == (keep and name ~= "a" and not false_steps.a))
        assert(weak.b == nil and weak.c == nil and weak.d == nil)
        log[#log + 1] = name
        local value = {name = name}
        weak[name] = value
        if false_steps[name] then return false end
        return value, "ignored second result"
    end
    collectgarbage("stop")
    local result, extra = run(step)
    assert(type(result) == expected_type and extra == nil)
    assert(result == false or result.name == expected:sub(-1))
    assert(table.concat(log) == expected)
    collectgarbage("restart")
end

check(choose, false, {d=true}, "abde", "table")
check(keep_entry, true, {d=true}, "abde", "table")
check(choose, false, {a=true}, "ae", "table")
check(keep_entry, true, {a=true}, "ae", "table")
check(choose, false, {b=true}, "abcd", "table")
check(keep_entry, true, {b=true}, "abcd", "table")
check(choose, false, {b=true,c=true}, "abce", "table")
check(keep_entry, true, {b=true,c=true}, "abce", "table")
check(choose, false, {}, "abd", "table")
check(keep_entry, true, {}, "abd", "table")
check(choose, false, {b=true,d=true}, "abcde", "table")
check(keep_entry, true, {b=true,d=true}, "abcde", "table")
check(choose, false, {d=true,e=true}, "abde", "boolean")
check(keep_entry, true, {d=true,e=true}, "abde", "boolean")
print("regress_562_short_circuit_entry_gc", "OK")
