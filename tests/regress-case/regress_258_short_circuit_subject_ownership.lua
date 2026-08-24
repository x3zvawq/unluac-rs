-- regress_258_short_circuit_subject_ownership#1: single-eval subject 必须保留 binding、live-out 与求值位置
-- unluac: expect-contains [[end)()]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
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
    print("regress_258_short_circuit_subject_ownership#3", outer(true))
end

do
    local old_print = print
    local function new_print(value)
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
end

do
    local count = 0
    local value = setmetatable({}, {
        __unm = function()
            count = count + 1
            return true
        end,
    })
    local function get()
        return value
    end
    local result = (-get()) and "yes" or "no"
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
    print("regress_258_short_circuit_subject_ownership#6", count)
end
