-- regress_172_temp_inline_eval_regions#1: while 外快照不能内联成每轮重读
local while_state = 1
local function while_snapshot()
    local snapshot = while_state
    while snapshot < 3 do
        while_state = while_state + 1
        if while_state > 10 then
            break
        end
    end
    return while_state
end
print("regress_172_temp_inline_eval_regions#1", while_snapshot())

-- regress_172_temp_inline_eval_regions#2: repeat 外快照不能内联成每轮重读
local repeat_state = 1
local function repeat_snapshot()
    local snapshot = repeat_state
    repeat
        repeat_state = repeat_state + 1
        if repeat_state > 10 then
            break
        end
    until snapshot >= 3
    return repeat_state
end
print("regress_172_temp_inline_eval_regions#2", repeat_snapshot())

-- regress_172_temp_inline_eval_regions#3: numeric-for 头保持 producer 的原始求值顺序
local numeric_log = {}
local function numeric_mark(tag, value)
    numeric_log[#numeric_log + 1] = tag
    return value
end
local numeric_limit = numeric_mark("limit", 2)
for _ = numeric_mark("start", 1), numeric_limit do
    break
end
print("regress_172_temp_inline_eval_regions#3", table.concat(numeric_log, ","))

-- regress_172_temp_inline_eval_regions#4: 多返回值保持 producer 的原始求值顺序
local return_log = {}
local function return_mark(tag)
    return_log[#return_log + 1] = tag
    return tag
end
local function return_order()
    local value = return_mark("value")
    return return_mark("other"), value
end
local first, second = return_order()
print(
    "regress_172_temp_inline_eval_regions#4",
    first,
    second,
    table.concat(return_log, ",")
)

-- regress_172_temp_inline_eval_regions#5: 方法 lookup 发生在显式参数前，不能越过前置 producer
local method_log = {}
local method_receiver = setmetatable({}, {
    __index = function(_, name)
        method_log[#method_log + 1] = "lookup:" .. name
        return function(_, value)
            method_log[#method_log + 1] = "call:" .. value
        end
    end,
})
local function method_mark()
    method_log[#method_log + 1] = "value"
    return "arg"
end
local method_value = method_mark()
method_receiver:run(method_value)
print(
    "regress_172_temp_inline_eval_regions#5",
    table.concat(method_log, ",")
)
