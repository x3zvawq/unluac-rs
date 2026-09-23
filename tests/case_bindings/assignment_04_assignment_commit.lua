-- Decision 可在终端直接写回现存 cell；逻辑叶的中间结果不能提前写回。
-- Boolean 参数与消息 COPY 共用完整 FASTCALL 帧，不留下预写占位和后继调用中转。
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=0]]
-- 先完成短路 RHS，再写回 captured cell；不为谓词 CALL 留下独立 callee 副本。
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=1]]
local function choose(flag, first)
    local current = "old"
    local trace = {}
    local function observe(label, result)
        assert(current == "old", "decision wrote the captured target before its RHS completed")
        trace[#trace + 1] = label
        return result
    end
    current = if flag
        then observe("first", first) and observe("second", false) or observe("fallback", "new")
        else observe("else", "other")
    return current, table.concat(trace, ",")
end

local a, at = choose(true, true)
assert(a == "new" and at == "first,second,fallback", at)
local b, bt = choose(true, false)
assert(b == "new" and bt == "first,fallback", bt)
local c, ct = choose(false, true)
assert(c == "other" and ct == "else", ct)
print("regress_572_decision_assignment_commit", "OK")
