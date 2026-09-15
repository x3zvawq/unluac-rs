-- regress_413_repeat_condition_binding_use: until shares the repeat body's local scope
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[1]] [[@proto=0]]

local provider = {}
local retired = setmetatable({}, { __mode = "v" })
local rounds = 0

function provider:make()
    local function finish(self)
        -- 调用后表不再保有方法；until 的 callee 准备必须覆盖原 CALL 留下的槽根。
        self.finish = nil
    end
    retired[1] = finish
    return {
        finish = finish,
    }
end

local function done(value)
    assert(type(value) == "table", "repeat condition lost its body-local binding")
    collectgarbage("collect")
    assert(retired[1] == nil, "until callee preparation must retire the previous method root")
    rounds = rounds + 1
    return rounds == 3
end

repeat
    local value = provider:make()
    value:finish()
until done(value)
assert(rounds == 3)

print("regress_413_repeat_condition_binding_use", "OK")
