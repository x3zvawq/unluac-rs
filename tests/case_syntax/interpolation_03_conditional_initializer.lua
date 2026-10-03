-- 奇偶选择的准备与后续插值复用同槽；恢复声明时仍须保留原 CALL/COPY。
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=1]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local decorate = run()
-- unluac-runtime: assert(decorate("k", 2) == "[k:even:2] len=8 brace={}")
-- unluac-runtime: assert(decorate("k", -3) == "[k:odd:-3] len=8 brace={}")
-- unluac-runtime: local trace = {}
-- unluac-runtime: local tag = setmetatable({}, {__tostring = function() trace[#trace + 1] = "tag"; return "tag" end})
-- unluac-runtime: local value = setmetatable({}, {
-- unluac-runtime:     __mod = function(_, divisor) assert(divisor == 2); trace[#trace + 1] = "mod"; return 0 end,
-- unluac-runtime:     __tostring = function() trace[#trace + 1] = "value"; return "value" end,
-- unluac-runtime: })
-- unluac-runtime: assert(decorate(tag, value) == "[tag:even:value] len=14 brace={}")
-- unluac-runtime: assert(table.concat(trace, "|") == "mod|tag|value")
-- unluac-runtime: local bad = setmetatable({}, {__mod = function() error("mod failed", 0) end})
-- unluac-runtime: local ok, err = pcall(decorate, tag, bad)
-- unluac-runtime: assert(not ok and string.find(err, "mod failed", 1, true))
-- unluac-runtime: assert(table.concat(trace, "|") == "mod|tag|value")
-- unluac-runtime: print(decorate("k", 2), decorate("k", -3), table.concat(trace, "|"))
return function(tag, value)
    local parity = if value % 2 == 0 then "even" else "odd"
    local body = `{tag}:{parity}:{value}`
    return `[{body}] len={#body} brace=\{}`
end
