-- 多结果 scratch 随后承接 captured local；未来捕获不属于先前的结果版本。
-- unluac: expect-contains [[first, second = pair(10)]] [[@debug=retained]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-contains [[left.value = left.value + 100]] [[@debug=retained]]
-- unluac: expect-contains [[return first, second, read]] [[@debug=retained]]
local function exercise(pair)
    local first, second = pair(1)
    first, second = pair(10)
    assert(first == 10 and second == 11)
    local left = { value = first }
    local right = { value = second }
    local function read()
        return left.value, right.value
    end
    left.value = left.value + 100
    return first, second, read
end

local calls = 0
local function pair(seed)
    calls = calls + 1
    return seed, seed + 1
end
local first, second, read = exercise(pair)
assert(first == 10 and second == 11 and calls == 2)
local a, b = read()
-- unluac: expect-contains [[assert(a == 110 and b == 11)]] [[@debug=retained]]
assert(a == 110 and b == 11)
print("writeback-before-capture", first, second, a, b, calls)

-- 复合字段操作数仍先读取再写回，两个元方法均只能执行一次。
-- unluac: expect-contains [[target.value = target.value + 100]] [[@debug=retained]]
local function update(target)
    target.value = target.value + 100
end
local reads, writes = 0, 0
local target = setmetatable({}, {
    __index = function(_, key)
        assert(key == "value" and writes == 0)
        reads = reads + 1
        return 5
    end,
    __newindex = function(_, key, value)
        assert(key == "value" and value == 105 and reads == 1)
        writes = writes + 1
    end,
})
update(target)
assert(reads == 1 and writes == 1)
