-- regress_239_lua55_degenerate_generic_scope: immediate-break不能把post-loop寄存器解释为迭代绑定
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[table.concat(r0_1, "|")]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[, nil, nil, ]]
-- unluac: expect-not-contains [[ = nil, nil]]
-- unluac: expect-not-contains [[in function()]]
local log = {}

local closer = setmetatable({}, {
    __close = function()
        log[#log + 1] = "close"
    end,
})

local function step()
    return 1
end

for value in step, nil, nil, closer do
    log[#log + 1] = value
    break
end

print("regress_239_lua55_degenerate_generic_scope", table.concat(log, "|"))
