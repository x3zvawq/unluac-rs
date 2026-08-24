-- regress_12_loop_break_shared_continuation#1: while 体内 break pad 带短路条件时不应拖垮外层结构恢复
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[in ipairs({]]
-- unluac: expect-not-contains [[ = ipairs]]
-- unluac: expect-not-contains [[unresolved(generic-for-call)]]
-- unluac: expect-not-contains [[unresolved(generic-for-loop cond)]]
-- unluac: expect-not-contains [[goto label_]]
-- unluac: expect-not-contains [[until true]]
local values = { "A==B", "BBBB" }

for _, span in ipairs({ { 1, 2 }, { 1, 2 } }) do
    while span[1] < span[2] do
        local left = values[span[1]]
        local right = values[span[2]]
        span[1] = span[1] + 1
        span[2] = span[2] - 1
        values[span[1] - 1] = right
        values[span[2] + 1] = left
    end
end

local map = { A = 1, B = 2 }
local output = {}

for index = 1, #values do
    local item = values[index]
    if type(item) == "string" then
        local size = string.len(item)
        local parts = {}
        local pos = 1
        local acc = 0
        local count = 0
        while pos <= size do
            local ch = string.sub(item, pos, pos)
            local mapped = map[ch]
            if mapped then
                acc = acc + mapped
                count = count + 1
                if count == 2 then
                    count = 0
                    table.insert(parts, string.char(acc))
                    acc = 0
                end
            elseif ch == "=" then
                table.insert(parts, string.char(acc))
                if pos >= size or string.sub(item, pos + 1, pos + 1) ~= "=" then
                    table.insert(parts, string.char(acc % 256))
                end
                break
            end
            pos = pos + 1
        end
        output[index] = table.concat(parts)
    end
end

print(
    "regress_12_loop_break_shared_continuation#1",
    #output[1],
    string.byte(output[1], 1, #output[1])
)
return output
