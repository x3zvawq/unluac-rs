-- regress_258_short_circuit_subject_ownership#1: single-eval subject 必须保留 binding、live-out 与求值位置
-- 快照可由局部 binding 或 IIFE 承担；以下断言验证实际值、次数与求值位置。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[and 1 == 1]]
-- unluac: expect-not-contains [[and true]]
do
    local x
    local old = {}
    local function get(self)
        return self == old
    end

    setmetatable(old, {
        __index = function()
            x = {}
            return get
        end,
    })

    x = old
    local receiver = x
    local result = x.f(receiver)
    assert(result == true and x ~= old, "receiver snapshot must precede __index mutation")
    print("regress_258_short_circuit_subject_ownership#1", result and x ~= old)
end

do
    local t = {
        f = function()
            return "old"
        end,
    }
    local result = t.f()
    local x = 1
    assert(result == "old" and x == 1)
    print("regress_258_short_circuit_subject_ownership#2", result == "old" and x == 1, result)
end

do
    local shared = true
    local function outer(param)
        local current = true
        local local_snapshot = current
        local param_snapshot = param
        local upvalue_snapshot = shared
        local function mutate()
            current = false
            param = false
            shared = false
        end
        mutate()
        local local_result = local_snapshot and "old" or "new"
        local param_result = param_snapshot and "old" or "new"
        local upvalue_result = upvalue_snapshot and "old" or "new"
        return local_result, param_result, upvalue_result, current, param, shared
    end
    local a, b, c, current, param, captured = outer(true)
    assert(a == "old" and b == "old" and c == "old", "snapshots must precede capture writes")
    assert(current == false and param == false and captured == false)
    print("regress_258_short_circuit_subject_ownership#3", a, b, c, current, param, captured)
end

do
    local old_print = print
    local observed
    local function new_print(value)
        observed = value
        old_print("regress_258_short_circuit_subject_ownership#4", "new", value)
    end
    local t = {
        f = function()
            print = new_print
            return "old"
        end,
    }
    local result = t.f()
    local x = 1
    print(result == "old" and x == 1)
    assert(observed == true, "print must be read after the call replaces it")
    print = old_print
end

do
    local count = 0
    local value = setmetatable({}, {
        __unm = function()
            count = count + 1
            return true
        end,
    })
    local gets = 0
    local function get()
        gets = gets + 1
        return value
    end
    local result = (-get()) and "yes" or "no"
    assert(gets == 1 and count == 1 and result == "yes", "subject and metamethod must each run once")
    print("regress_258_short_circuit_subject_ownership#5", count, result)
end

do
    local count = 0
    local value = setmetatable({}, {
        __unm = function()
            count = count + 1
            return true
        end,
    })
    local outer, inner = true, true
    if outer then
        local unused = -value
        if inner then
            print("regress_258_short_circuit_subject_ownership#6", "inside")
        end
    end
    assert(count == 1, "unused metamethod result must retain its evaluation")
    print("regress_258_short_circuit_subject_ownership#6", count)
end
