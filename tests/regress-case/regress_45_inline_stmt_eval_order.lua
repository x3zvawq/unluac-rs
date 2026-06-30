-- regress_45_inline_stmt_eval_order#1: inline-exprs 不能把前置调用移到 call receiver/callee 之后

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
print("regress_45_inline_stmt_eval_order#1", table.concat(log, ","), value)
