local obj = {
    seed = 0x2A,
    rows = {
        { 4, 7, 9 },
        { 3, 12, 5 },
    },
}

function obj:fold(row_index, step)
    local row = self.rows[row_index]
    local total = self.seed ~ row_index

    for i = 1, #row do
        local base = row[i]
        local mixed = ((base << step) | (self.seed >> (i - 1))) ~ (row_index * i)

        if (mixed & 0x03) == 0 then
            total = total + (mixed // (i + 1))
        else
            total = total + (mixed % (i + 3))
        end
    end

    self.rows[row_index][#row + 1] = total & 0xFF
    return self.rows[row_index][#row], self.rows[row_index][1] ~ total
end

local x1, y1 = obj:fold(1, 2)
local x2, y2 = obj:fold(2, 1)

print("method-bit", x1, y1, x2, y2, obj.rows[1][4], obj.rows[2][4])
