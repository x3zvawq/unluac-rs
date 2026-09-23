-- CLOSE 后的多返回结果保持各自 cell 身份，后续帧不继承空声明造成的永久占位。
-- unluac: expect-contains [[= setmetatable({}, {]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
do
    local first, second, captured = 0, 1, 2
    local function advance()
        captured = captured + first + second
        return captured
    end
    assert(advance() == 3)
    PREVIOUS_READER = advance
    print(first, second, captured)
end

local count = 0
local function values()
    return 7, 8
end
local first, second = values()
assert(first == 7 and second == 8)
local third, fourth = values()
assert(third == 7 and fourth == 8)
print(first, second, third, fourth)
local value = setmetatable({}, {
    __unm = function()
        count = count + 1
        return true
    end,
})
assert(type(value) == "table")
assert(PREVIOUS_READER() == 4)
PREVIOUS_READER = nil
local result = -value
assert(count == 1 and result == true)
print("capture_20_reused_result_slot", count, result)
