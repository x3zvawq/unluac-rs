-- base 与动态 key 都可触发回调；key 改写来源不能让最终读取换到新表。
-- unluac: expect-contains [=[return self.values[self.index]]=] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
local function read(self)
    return self.values[self.index]
end
local events = {}
local values = setmetatable({}, {
    __index = function(_, key)
        events[#events + 1] = "lookup:" .. key
        return 73
    end,
})
local replacement = {chosen = -1}
local receiver = setmetatable({}, {
    __index = function(_, key)
        if key == "values" then
            events[#events + 1] = "base"
            return values
        end
        assert(key == "index")
        events[#events + 1] = "key"
        values = replacement
        return "chosen"
    end,
})
assert(read(receiver) == 73)
assert(table.concat(events, ",") == "base,key,lookup:chosen")
assert(values == replacement)
print("nested-dynamic-return", table.concat(events, ","))
