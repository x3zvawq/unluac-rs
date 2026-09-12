-- 入口 TEST 后的各 successor 都先覆盖同槽 callee：不能额外保活第一次调用结果。
local function choose(step)
    return (step("a") and (step("b") or step("c")) and step("d")) or step("e")
end

-- 独立源码 local 处于后续 call frame 下方，不能套用短路入口的覆盖证书。
local function keep_entry(step)
    local saved = step("a")
    return (saved and (step("b") or step("c")) and step("d")) or step("e")
end

local function check(run, keep)
    local weak = setmetatable({}, {__mode = "v"})
    local log = {}
    local function step(name)
        collectgarbage("collect")
        collectgarbage("collect")
        assert((weak.a ~= nil) == (keep and name ~= "a"))
        assert(weak.b == nil and weak.c == nil and weak.d == nil)
        log[#log + 1] = name
        local value = {}
        weak[name] = value
        if name == "d" then return false end
        return value, "ignored second result"
    end
    collectgarbage("stop")
    assert(run(step))
    assert(table.concat(log) == "abde")
    collectgarbage("restart")
end

check(choose, false)
check(keep_entry, true)
print("regress_562_short_circuit_entry_gc", "OK")
