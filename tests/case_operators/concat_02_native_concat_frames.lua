-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=7]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=7]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=7]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=7]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=7]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[function]] [[10]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[20]]
-- CONCAT 的 operand 左到右求值，合并右到左；中间根的存活由原缓冲槽决定。
-- unluac: expect-contains [[("a") .. ":" ..]]
local weak = setmetatable({}, {__mode = "v"})
local meta = {}
local pieces, merges = 0, 0
local produced = ""
local function label(value)
    return type(value) == "table" and value.name or value
end
meta.__concat = function(left, right)
    merges = merges + 1
    collectgarbage("collect")
    print("concat", label(left), label(right), weak.a ~= nil, weak.b ~= nil, weak.c ~= nil)
    return "(" .. label(left) .. label(right) .. ")"
end
local function piece(name)
    pieces = pieces + 1
    produced = produced .. name
    local value = setmetatable({name = name}, meta)
    weak[name] = value
    print("piece", name)
    return value, "discarded"
end
local function joined(factory)
    return factory("a") .. ":" .. factory("b") .. ":" .. factory("c")
end
local function separated(factory)
    local prefix = factory("a") .. factory("b")
    print("between")
    return prefix .. factory("c")
end
local function stored(factory)
    local value = factory("a") .. ":" .. factory("b") .. ":" .. factory("c")
    print("stored", value)
end
print("joined", joined(piece))
assert(pieces == 3 and merges == 3 and produced == "abc")
collectgarbage("collect")
print("separated", separated(piece))
assert(pieces == 6 and merges == 5 and produced == "abcabc")
collectgarbage("collect")
stored(piece)
assert(pieces == 9 and merges == 8 and produced == "abcabcabc")

-- 低槽左值在 CONCAT 后由比较读取；元方法改写捕获 cell，不能提前冻结 lhs。
-- 同一 CONCAT 仍从右到左合并，并且只把最终 Boolean 交给一次调用。
-- unluac: expect-contains [[observe(expected == left .. middle .. right)]] [[@debug=retained]]
local function comparison_argument()
    local expected = "before"
    local events = ""
    local middle = {}
    local right = setmetatable({}, { __concat = function(lhs, rhs)
        assert(lhs == middle)
        events = events .. "right;"
        return "joined"
    end })
    local left = setmetatable({}, { __concat = function(lhs, rhs)
        assert(rhs == "joined")
        events = events .. "left;"
        expected = "after"
        return "after"
    end })
    local function observe(value)
        assert(value == true)
        events = events .. "observe;"
    end
    observe(expected == left .. middle .. right)
    assert(events == "right;left;observe;")
    print("concat-comparison", events, expected)
end
comparison_argument()

-- 每次调用重新建立操作数根；额外返回值不能成为 CONCAT 的下一项。
assert(joined(piece) == "(a:(b(:c)))")
assert(separated(piece) == "((ab)c)")
assert(pieces == 15 and merges == 13 and produced == "abcabcabcabcabc")
assert(select("#", joined(piece)) == 1)
assert(select("#", stored(piece)) == 0)
assert(pieces == 21 and merges == 19 and produced == "abcabcabcabcabcabcabc")
assert(select("#", comparison_argument()) == 0)
