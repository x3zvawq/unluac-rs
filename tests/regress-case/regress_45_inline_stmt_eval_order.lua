-- regress_45_inline_stmt_eval_order#1:
-- inline-exprs 不能把前置调用移到 call receiver/callee 之后；
-- method alias 也不能因两个调用参数相同而合并 receiver 求值。

local log = {}

local function mark(tag)
    log[#log + 1] = tag
    return {
        method = function(self)
            log[#log + 1] = "method"
            return self.tag
        end,
        tag = tag,
    }
end

local receiver = mark("alias")
local value = mark("callee").method(receiver)
local distinct_log = table.concat(log, ",")
local distinct_value = value

log = {}
receiver = mark("same")
value = mark("same").method(receiver)

print(
    "regress_45_inline_stmt_eval_order#1",
    distinct_log,
    distinct_value,
    value,
    table.concat(log, ",")
)
