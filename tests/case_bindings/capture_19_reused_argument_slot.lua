-- 旧闭包关闭后，新的参数帧可复用其物理槽，不能沿用旧 cell 或假定 epoch 为零。
-- unluac: expect-contains [[= setmetatable({}, {]]
do
    local first, second, captured = 0, 1, 2
    local function advance()
        captured = captured + 1
        return captured
    end
    assert(advance() == 3)
    PREVIOUS_READER = advance
    print(first, second, captured)
end
local count = 0
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
print("capture_19_reused_argument_slot", count, result)
