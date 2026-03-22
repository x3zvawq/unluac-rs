local function analyze(limit)
    local out = {}

    for i = 1, limit do
        local j = 0

        while j < 4 do
            j = j + 1

            if (i + j) % 2 == 0 then
                out[#out + 1] = i * 10 + j
            else
                repeat
                    out[#out + 1] = i + j
                    break
                until false
            end

            if j == i then
                break
            end
        end
    end

    return table.concat(out, "|")
end

print("flow-mesh", analyze(3))
