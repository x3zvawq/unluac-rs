-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]
-- regress_240_lua55_tforprep_swap: TFORPREP交换前的control/closing才是源码迭代器pack
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[in function(]]
-- unluac: expect-not-contains [[, (setmetatable]]
local trace = {}

local closer = setmetatable({ tag = "K" }, {
    __close = function(self, failure)
        assert(failure == nil)
        trace[#trace + 1] = "close:" .. self.tag
    end,
})

local function step(state, control)
    trace[#trace + 1] = "call:" .. state .. ":" .. control
end

for _ in step, "S", "C", closer do
    error("unreachable")
end

local observed = table.concat(trace, "|")
assert(observed == "call:S:C|close:K")
print("regress_240_lua55_tforprep_swap", observed)
