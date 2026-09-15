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
local while_result = while_snapshot()
assert(while_result == 11)
print("regress_172_temp_inline_eval_regions#1", while_result)

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
local repeat_result = repeat_snapshot()
assert(repeat_result == 11)
print("regress_172_temp_inline_eval_regions#2", repeat_result)

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
assert(table.concat(numeric_log, ",") == "limit,start")
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
assert(first == "other" and second == "value" and table.concat(return_log, ",") == "value,other")
print(
    "regress_172_temp_inline_eval_regions#4",
    first,
    second,
    table.concat(return_log, ",")
)

-- regress_172_temp_inline_eval_regions#5: 方法 lookup 发生在显式参数前，不能越过前置 producer
-- unluac: expect-not-line [[local r0_15 = r0_13]]
-- unluac: expect-not-line [[local r0_16 = r0_14]]
-- unluac: expect-not-line [[local r0_17 = r0_15]]
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
assert(table.concat(method_log, ",") == "value,lookup:run,call:arg")
print(
    "regress_172_temp_inline_eval_regions#5",
    table.concat(method_log, ",")
)

-- 每轮先保存条件，回调修改原 binding 不能改变本轮的条件快照。
do
    local ready, ticks = false, 0
    local function tick() ticks = ticks + 1; ready = true end
    repeat
        local stop = ready
        tick()
    until stop
    assert(ticks == 2)
    print("regress_172_temp_inline_eval_regions#5", ticks)
end

-- 同一合同也适用于父 frame 的 upvalue；它没有当前函数的物理 home。
do
    local ready, ticks = false, 0
    local function tick() ticks = ticks + 1; ready = true end
    local function run()
        repeat
            local stop = ready
            tick()
        until stop
    end
    run()
    assert(ticks == 2)
    print("regress_172_temp_inline_eval_regions#6", ticks)
end
