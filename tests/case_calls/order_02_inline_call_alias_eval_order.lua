-- regress_147_inline_call_alias_eval_order#1: sink 参数顺序不得重排前置调用
-- unluac: expect-order [[("first")]] [[("second")]]
-- unluac: expect-order [[("before")]] [[("keep")]]
-- unluac: expect-order [[("keep")]] [[("after")]]
local log = {}

local function mark(value)
    log[#log + 1] = value
    return value
end

local first = mark("first")
local second = mark("second")
print(second, first, 0)
assert(table.concat(log, ",") == "first,second")
print(table.concat(log, ","))

-- regress_147_inline_call_alias_eval_order#2: 未删除的声明必须阻断调用搬运
log = {}
local before = mark("before")
local keep = mark("keep")
local after = mark("after")
assert(table.concat(log, ",") == "before,keep,after")
print(before, after, 0)
print(keep, table.concat(log, ","))
