-- 算术结果在原求值完成后安装到上值；元方法对同一 cell 的写入不能覆盖最终结果。
-- unluac: expect-contains [[value = value + 1]] [[@debug=retained]]
-- unluac: expect-contains [[original = setmetatable({}, {]] [[@debug=retained]]
local value
local original
local result = {}
local calls = 0
local function update()
    value = value + 1
end
original = setmetatable({}, {
    __add = function(lhs, rhs)
        calls = calls + 1
        assert(lhs == original and rhs == 1 and value == original)
        value = "during-add"
        return result
    end,
})
value = original
update()
assert(value == result and calls == 1)
value = 3
update()
assert(value == 4 and calls == 1)
print("arithmetic-upvalue-writeback", calls, value)
