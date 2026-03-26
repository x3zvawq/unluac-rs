local function make_mesh(seed: number): () -> string
    local total: number = seed
    local captures = {}

    for row = 1, 4 do
        local inner: number = row

        for col = 1, 5 do
            if (row + col) % 3 == 0 then
                total += row
                continue
            end

            inner += col
            total += if inner % 2 == 0 then inner else col
        end

        local saved_row: number = row
        local saved_inner: number = inner
        local saved_total: number = total
        captures[#captures + 1] = function(): string
            return `r{saved_row}:{saved_inner}:{saved_total}`
        end
    end

    return function(): string
        local out = {}

        for index, capture in ipairs(captures) do
            out[index] = capture()
        end

        return table.concat(out, ";")
    end
end

print(make_mesh(10)())
