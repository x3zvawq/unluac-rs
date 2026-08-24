-- regress_45_inline_stmt_eval_order#1:
-- inline-exprs 不能把前置调用移到 call receiver/callee 之后；
-- method alias 也不能因两个调用参数相同而合并 receiver 求值。
-- unluac: expect-not-contains [[local r0_6 = r0_4]]

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

local function written_source_keeps_snapshot()
    local source = { tag = "before" }
    local snapshot = source
    source = { tag = "after" }
    return snapshot.tag, source.tag
end

local function captured_source_keeps_snapshot()
    local source = { tag = "captured" }
    local snapshot = source
    local function replace()
        source = { tag = "replaced" }
    end
    replace()
    return snapshot.tag, source.tag
end

print("regress_45_inline_stmt_eval_order#2", written_source_keeps_snapshot())
print("regress_45_inline_stmt_eval_order#3", captured_source_keeps_snapshot())
