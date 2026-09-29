-- regress_317_lua51_loop_region_ownership: 短路 if 的 else 数值循环不能把退出边归给外层分支
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[if not (issue17_a or issue17_b) then]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[break]]
local function run()
    if issue17_a or issue17_b then
        local unused
    else
        for index = 1, 2 do
        end
    end
    print("regress_317_lua51_loop_region_ownership", "done")
end

-- 独立环境记录实际全局读取；a 为真时不得读取 b，空循环仍由 AST 断言保留。
local function observe(a, b, expected)
    local trace = {}
    setfenv(run, setmetatable({print = print}, {__index = function(_, key)
        trace[#trace + 1] = key
        if key == "issue17_a" then
            return a
        end
        assert(key == "issue17_b")
        return b
    end}))
    run()
    assert(table.concat(trace, ",") == expected)
end
observe(false, false, "issue17_a,issue17_b")
observe(false, true, "issue17_a,issue17_b")
observe(true, false, "issue17_a")
observe(true, true, "issue17_a")
observe(nil, nil, "issue17_a,issue17_b")
observe(nil, 0, "issue17_a,issue17_b")
observe(false, "", "issue17_a,issue17_b")
observe(0, false, "issue17_a")
observe("", nil, "issue17_a")
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
