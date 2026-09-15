-- Boolean 参数的 CALL operands 各占结果槽之上的一格；比较元方法与两次调用顺序都可观察。
local metatable = {
    __eq = function(left, right)
        print("equal", left.name, right.name)
        return true
    end,
}
local function make(name)
    print("make", name)
    return setmetatable({ name = name }, metatable), "discarded"
end
local function compare(factory, consume)
    consume("result", factory("a") == factory("b"), factory("c") ~= factory("d"))
end
getfenv().comparison_frame = compare
getfenv().comparison_frame(make, print)

-- 结果槽的旧对象必须活到比较元方法返回；不能提前写入预设 Boolean。
local weak = setmetatable({}, { __mode = "v" })
local observations = 0
local comparison_meta = {
    __eq = function()
        for index = 1, 20000 do
            local garbage = { index, index + 1, index + 2 }
        end
        assert(weak[1] ~= nil, "comparison overwrote its old result root before the callback")
        observations = observations + 1
        return true
    end,
}
local function make_root()
    local value = {}
    weak[1] = value
    return value
end
local function overwrite(left, right, factory)
    local value = factory()
    value = left == right
    return value
end
getfenv().comparison_overwrite = overwrite
print("overwrite", getfenv().comparison_overwrite(
    setmetatable({}, comparison_meta), setmetatable({}, comparison_meta), make_root), observations)
