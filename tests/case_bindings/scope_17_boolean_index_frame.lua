-- nil/Boolean 的多次原写在同一内层绑定中保留；后继索引帧复用原槽时结束声明。
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-not-contains [[ = table.concat]]
-- unluac: expect-contains [[return table.concat(]]
local function trace_path(flag)
    local trace = {}
    do
        local unused = nil
        if flag then unused = true else unused = false end
        trace[#trace + 1] = "a"
        if not flag then unused = true else unused = false end
    end
    if flag then
        trace[#trace + 1] = "T"
    else
        trace[#trace + 1] = "F"
    end
    return table.concat(trace)
end
assert(trace_path(true) == "aT")
assert(trace_path(false) == "aF")
print("boolean_index_frame", "OK")
