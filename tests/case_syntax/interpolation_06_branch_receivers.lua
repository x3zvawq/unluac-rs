-- 两臂 SELF receiver 的同槽准备仍保留独立 Def，不能先被循环 carrier 合并。
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=2]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local factory = run()
-- unluac-runtime: local named, plain = factory("p"), factory(nil)
-- unluac-runtime: assert(named({4, -2, 7}) == "p-1:4|p-3:13")
-- unluac-runtime: assert(plain({4, -2, 7}) == "slot-1:4|slot-3:13")
-- unluac-runtime: assert(plain({1, -3, 2}) == "slot-1:14|slot-3:19")
-- unluac-runtime: assert(plain({}) == "" and plain({0}) == "slot-1:19")
-- unluac-runtime: local dispatch, nested, calls = nil, nil, 0
-- unluac-runtime: local prefix = setmetatable({}, {__tostring = function()
-- unluac-runtime:     calls += 1
-- unluac-runtime:     if calls == 1 then nested = dispatch({10}) end
-- unluac-runtime:     return "P"
-- unluac-runtime: end})
-- unluac-runtime: dispatch = factory(prefix)
-- unluac-runtime: local outer = dispatch({1, 2})
-- unluac-runtime: assert(outer == "P-1:1|P-2:13" and nested == "P-1:11" and calls == 3)
-- unluac-runtime: print(outer, nested, calls)
return function(prefix)
    local counter = 0
    return function(values)
        local parts = {}
        for index, value in ipairs(values) do
            if value < 0 then
                counter += -value
                continue
            end
            counter += value
            parts[#parts + 1] = if prefix then `{prefix}-{index}:{counter}` else `slot-{index}:{counter}`
        end
        return table.concat(parts, "|")
    end
end
