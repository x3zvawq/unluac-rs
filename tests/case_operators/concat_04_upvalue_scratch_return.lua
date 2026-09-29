-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- CONCAT 先完整写回上值，随后算术复用结果槽；元方法可改写 cell 并观察原临时根。
-- unluac: expect-contains [[state = state .. "suffix"]] [[@debug=retained]]
-- unluac: expect-contains [[return first + second + third]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-contains [[assert(state == weak[1] and type(state) == "table")]] [[@debug=retained]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
-- unluac: expect-instruction-count [[call]] [[27]] [[@variant=O2]]
-- unluac: expect-contains [[assert(update(operand, 2, 3) == operand)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[= print]] [[@variant=O2]]
local state
local function update(first, second, third)
    state = state .. "suffix"
    return first + second + third
end

local weak = setmetatable({}, { __mode = "v" })
local concats, additions = 0, 0
local input = setmetatable({}, {
    __concat = function(left, right)
        assert(state == left and right == "suffix")
        concats = concats + 1
        state = "during-concat"
        local result = {}
        weak[1] = result
        return result
    end,
})
local operand = setmetatable({}, {
    __add = function(left, right)
        additions = additions + 1
        assert(right == additions + 1)
        if additions == 1 then
            assert(state == weak[1] and type(state) == "table")
        else
            assert(state == nil)
        end
        state = nil
        collectgarbage("collect")
        print("concat-scratch-root", additions, weak[1] ~= nil)
        return left
    end,
})
state = input
assert(update(operand, 2, 3) == operand)
assert(concats == 1 and additions == 2 and state == nil)
state = "plain"
assert(update(1, 2, 3) == 6 and state == "plainsuffix")
print("concat-upvalue-return", concats, additions)

-- CONCAT 的写回先于算术：后续算术失败也不能撤销已经写回的状态。
concats, additions = 0, 0
state = input
assert(select("#", update(operand, 2, 3)) == 1)
assert(concats == 1 and additions == 2 and state == nil)
state = 0
assert(not pcall(update, false, 2, 3))
assert(state == "0suffix" and concats == 1 and additions == 2)
state = nil
assert(not pcall(update, operand, 2, 3))
assert(state == nil and concats == 1 and additions == 2)
state = ""
assert(update(-1, 2, -3) == -2 and state == "suffix")
concats, additions = 0, 0
state = input
assert(not pcall(update, operand, 2, false))
assert(concats == 1 and additions == 2 and state == nil)
