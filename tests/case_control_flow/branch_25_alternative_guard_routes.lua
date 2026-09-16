-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- Recover success/failure guard routes without evaluating the right side twice.
local function check(enabled, health, roll)
    if enabled then
        local n = roll
        if (health < 0.5 and n <= 90) or n <= 45 then
            print("bonus")
        end
    end
    print("tail")
end
for enabled = 0, 1 do
    for health = 1, 3, 2 do
        for roll = 44, 92, 2 do
            check(enabled == 1, health / 4, roll)
        end
    end
end
