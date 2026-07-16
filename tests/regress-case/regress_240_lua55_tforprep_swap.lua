-- regress_240_lua55_tforprep_swap: TFORPREP交换前的control/closing才是源码迭代器pack
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[, "S", "C", ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local trace = {}

local closer = setmetatable({ tag = "K" }, {
    __close = function(self)
        trace[#trace + 1] = "close:" .. self.tag
    end,
})

local function step(state, control)
    trace[#trace + 1] = "call:" .. state .. ":" .. control
end

for _ in step, "S", "C", closer do
    error("unreachable")
end

print("regress_240_lua55_tforprep_swap", table.concat(trace, "|"))
