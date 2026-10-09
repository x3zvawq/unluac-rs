-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[27]] [[@proto=1]] [[@dialect=lua5.1]]
local function calculate(self)
    local bases = { 1, 3.7, 13.69, 50.65, 187.42, 693.44, 2565.73, 9493.19 }
    local ids = { 24442, 24443, 24444, 24445, 24446, 24447, 24448, 24449 }
    local rate, quality, value
    local scale = 0.42
    local sum = 0
    local multiplier = 0.37037037037037035
    local fraction, integer
    local counts = { 0, 0, 0, 0, 0, 0, 0, 0 }
    local result = {}
    for level = 1, self.nStrengthLevel do
        if level < 8 then
            rate = 1 + 0.5 * (6 - level)
        else
            rate = 1.05 / 2 ^ (level - 7)
        end
        if self.nLevel * self.nQuality < 6400 then
            quality = 0.8 + math.min(0.4, 160 / self.nLevel / self.nQuality)
        elseif self.nLevel * self.nQuality < 16800 then
            quality = 0.474286 + 2244.571 / self.nLevel / self.nQuality
        else
            quality = 0.377629 + 3868.398 / self.nLevel / self.nQuality
        end
        value = rate / multiplier / scale / quality * (1 + 1 / multiplier) ^ (level - 1)
        if self.nStrengthLevel >= 6 then
            value = value * 0.83
        end
        sum = sum + value
    end
    if self.nDetail == 9 then
        sum = sum / 10
    end
    for index = 1, 6 do
        integer, fraction = math.modf(sum / bases[7 - index])
        counts[7 - index] = integer
        sum = bases[7 - index] * fraction
        if counts[7 - index] ~= 0 then
            table.insert(result, { 5, ids[7 - index], counts[7 - index] })
        end
    end
    return result
end
local expected = {
    "5,24445,1;5,24444,2;5,24443,1;5,24442,2",
    "5,24447,8;5,24445,1;5,24444,3;5,24443,1;5,24442,1",
    "5,24447,269;5,24446,1;5,24445,2;5,24444,2;5,24443,2;5,24442,2",
    "",
}
for index, settings in ipairs({
    { nStrengthLevel = 2, nLevel = 50, nQuality = 10, nDetail = 0 },
    { nStrengthLevel = 8, nLevel = 100, nQuality = 100, nDetail = 9 },
    { nStrengthLevel = 9, nLevel = 200, nQuality = 200, nDetail = 0 },
    { nStrengthLevel = 0, nLevel = 50, nQuality = 10, nDetail = 0 },
}) do
    local result = calculate(settings)
    local rows = {}
    for position, row in ipairs(result) do
        assert(#row == 3)
        rows[position] = table.concat(row, ",")
    end
    assert(table.concat(rows, ";") == expected[index])
    print("branched-loop-prefix", index, table.concat(rows, ";"))
end
