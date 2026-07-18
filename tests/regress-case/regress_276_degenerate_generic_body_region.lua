-- regress_276_degenerate_generic_body_region: branch前缀与nested loop同属退化for状态
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[return ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(log_body, xs)
    local x = 0
    for key in pairs(xs) do
        if log_body then
            print("body", x)
        end
        repeat
            x = x + 1
        until xs[x]
        break
    end
    return x
end

print(
    "regress_276_degenerate_generic_body_region",
    run(false, {}),
    run(false, { true }),
    run(true, { true })
)
