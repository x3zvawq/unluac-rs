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

print("regress_27_while_true_latch_tail#1", scan_until_terminal(4))
