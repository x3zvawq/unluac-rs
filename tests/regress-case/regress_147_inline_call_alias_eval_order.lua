-- regress_147_inline_call_alias_eval_order#1: sink 参数顺序不得重排前置调用
local log = {}

local function mark(value)
    log[#log + 1] = value
    return value
end

local first = mark("first")
local second = mark("second")
print(second, first, 0)
print(table.concat(log, ","))

-- regress_147_inline_call_alias_eval_order#2: 未删除的声明必须阻断调用搬运
log = {}
local before = mark("before")
local keep = mark("keep")
local after = mark("after")
print(before, after, 0)
print(keep, table.concat(log, ","))
