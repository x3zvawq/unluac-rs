-- regress_27_while_true_latch_tail#1: while-true jump latch tail should not fall back to goto
-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[+ 1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function scan_until_terminal(limit)
    local values = { "a", "b", "c", "d" }
    local i = 0
    while true do
        local current = values[i + 1]
        if current == nil then
            current = values[1]
            i = 0
        end
        if current == "c" then
            print("regress_27_while_true_latch_tail#1", current)
            return current
        end
        if i == limit then
            print("regress_27_while_true_latch_tail#1", "limit")
            return current
        end
        i = i + 1
    end
end

local result = scan_until_terminal(4)
assert(result == "c")
print("regress_27_while_true_latch_tail#1", result)
assert(scan_until_terminal(0) == "a")
assert(scan_until_terminal(1) == "b")
-- terminal 检查先于 limit，limit=2 必须打印 c 而非 limit。
assert(scan_until_terminal(2) == "c")
assert(scan_until_terminal(-1) == "c")
assert(scan_until_terminal(nil) == "c")
assert(scan_until_terminal(false) == "c")
assert(scan_until_terminal("1") == "c")
-- 固定表会在 c 返回，nil/reset 分支不可由 limit 触发，但必须保留原检查。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
