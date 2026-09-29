-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[5]]
-- unluac: expect-ast-count [[do-block]] [[0]]
-- unluac: expect-ast-count [[error]] [[0]]
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

local closer = setmetatable({ tag = "closer" }, {
    __close = function(self, failure)
        assert(self.tag == "closer" and failure == nil)
        log[#log + 1] = "close"
    end,
})

local function step(state, control)
    assert(state == nil and control == nil)
    log[#log + 1] = "step"
    return 1
end

for value in step, nil, nil, closer do
    log[#log + 1] = value
    break
end

local observed = table.concat(log, "|")
assert(observed == "step|1|close")
print("regress_239_lua55_degenerate_generic_scope", observed)
