-- base 与动态 key 都可触发回调；key 改写来源不能让最终读取换到新表。
-- unluac: expect-contains [=[return self.values[self.index]]=] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
local function read(self)
    return self.values[self.index]
end
-- 动态 key 是既有参数/循环绑定时直接读取低槽，复合 base 仍先在原高槽求值。
-- unluac: expect-contains [=[return self.values[key]]=] [[@debug=retained]]
-- unluac: expect-contains [=[t[i][j]]=] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=3]] [[@dialect=luau]]
-- O2 展开的连续更新仍各自保留未赋值路径，不因初始化同块而逐轮变成自赋值选择式。
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=0]] [[@variant=O2]] [[@debug=retained]]
-- O2 将 key 参数替成字符串，仍保留 IndexExpr 的高槽 base，不能改成复用结果槽的点语法。
-- unluac: expect-contains [=[values["chosen"]]=] [[@dialect=luau]] [[@variant=O2]]
local function read_key(self, key)
    return self.values[key]
end
local function find(t, limit)
    local found = 0
    for i = 1, limit do
        for j = 1, limit do
            if t[i][j] == "target" then
                found = i * 10 + j
            end
        end
    end
    return found
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
events = {}
assert(read_key(receiver, "chosen") == -1)
assert(table.concat(events, ",") == "base")
events = {}
local rows = {}
for i = 1, 2 do
    rows[i] = setmetatable({}, {
        __index = function(_, j)
            events[#events + 1] = "key:" .. j
            return i + j == 3 and "target" or "skip"
        end,
    })
end
local grid = setmetatable({}, {
    __index = function(_, i)
        events[#events + 1] = "base:" .. i
        return rows[i]
    end,
})
assert(find(grid, 2) == 21)
assert(table.concat(events, ",") == "base:1,key:1,base:1,key:2,base:2,key:1,base:2,key:2")
print("nested-dynamic-key", table.concat(events, ","))
