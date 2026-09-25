-- 空数组没有 SETLIST，仍需与相邻非空数组一起恢复原 iterator 初始化帧。
-- unluac: expect-contains [[in ipairs({ {}, { 10 }, { 20, 30 } })]]
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-not-contains [[= ipairs]]
local total = 0
for index, row in ipairs({ {}, { 10 }, { 20, 30 } }) do
    print("empty-array-row", index, #row)
    total = total + #row
end
assert(total == 3)
print("empty-array-frame", total)
