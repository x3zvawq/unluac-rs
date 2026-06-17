-- regress_35_multi_entry_loop_state#1: 多入口 while 应复用共同入口初值作为 loop state
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

local function count_previous_levels(meta, start_index, unlocked)
    local count = 1
    local index = start_index - 1
    if not meta or not meta.isAlternativePathLevel then
        while index > 0 do
            if unlocked[index] then
                index = 0
            else
                count = count + 1
                index = index - 1
            end
        end
    end
    return count
end

print("regress_35_multi_entry_loop_state#1", count_previous_levels({ isAlternativePathLevel = true }, 4, {}))
print("regress_35_multi_entry_loop_state#2", count_previous_levels(nil, 4, {}))
