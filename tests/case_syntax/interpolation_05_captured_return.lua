-- 插值 CALL 的低槽结果 COPY 已吸收时，返回帧仍须消费全部上值准备。
-- unluac: expect-ast-max [[local-binding]] [[0]] [[@proto=2]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local factory = run()
-- unluac-runtime: local trace, update = {}, nil
-- unluac-runtime: local first = setmetatable({}, {__tostring = function() trace[#trace + 1] = "first"; update("new"); return "a" end})
-- unluac-runtime: local old = setmetatable({}, {__tostring = function() trace[#trace + 1] = "old"; return "old" end})
-- unluac-runtime: local last = setmetatable({}, {__tostring = function() trace[#trace + 1] = "last"; return "c" end})
-- unluac-runtime: local read
-- unluac-runtime: read, update = factory(first, old, last)
-- unluac-runtime: assert(read() == "ra:old:c")
-- unluac-runtime: assert(table.concat(trace, "|") == "first|old|last")
-- unluac-runtime: assert(read() == "ra:new:c")
-- unluac-runtime: assert(table.concat(trace, "|") == "first|old|last|first|last")
-- unluac-runtime: local plain = factory(nil, false, 2)
-- unluac-runtime: assert(plain() == "rnil:false:2")
-- unluac-runtime: print(plain(), table.concat(trace, "|"))
return function(a, b, c)
    return function()
        return `r{a}:{b}:{c}`
    end, function(value)
        b = value
    end
end
