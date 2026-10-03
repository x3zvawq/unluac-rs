-- 已完整的首个选择表达式不占用后继选择的准备恢复机会。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=1]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local route = run()
-- unluac-runtime: assert(route(3, "named") == "router named pos 3")
-- unluac-runtime: assert(route(0, nil) == "router anon zero 0")
-- unluac-runtime: assert(route(-2, false) == "router anon neg -2")
-- unluac-runtime: local trace = {}
-- unluac-runtime: local name = setmetatable({}, {__tostring = function() trace[#trace + 1] = "name"; return "name" end})
-- unluac-runtime: assert(route(3, name) == "router name pos 3")
-- unluac-runtime: assert(table.concat(trace, "|") == "name")
-- unluac-runtime: local invalid = setmetatable({}, {__lt = function() error("unexpected lt", 0) end})
-- unluac-runtime: local ok, err = pcall(route, invalid, name)
-- unluac-runtime: assert(not ok and string.find(err, "compare number < table", 1, true))
-- unluac-runtime: assert(table.concat(trace, "|") == "name")
-- unluac-runtime: print(route(3, "named"), route(0, nil), route(-2, false), table.concat(trace, "|"))
return function(total, name)
    local label = if name then name else "anon"
    local mode = if total > 0 then "pos" elseif total == 0 then "zero" else "neg"
    return `router {label} {mode} {total}`
end
