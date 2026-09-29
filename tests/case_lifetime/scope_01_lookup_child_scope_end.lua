-- regress_396_lookup_child_scope_end: child lookup root ends at the proven home reuse boundary
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[if]] [[1]]

local finalized = 0
local entered = 0
local mt = {
    __gc = function()
        finalized = finalized + 1
    end,
}
local weak = setmetatable({}, { __mode = "v" })
local owner = setmetatable({}, mt)
weak.value = owner
assert(weak.value == owner)
owner = nil

if finalized == 0 then
    local lookup = weak.value
    collectgarbage("collect")
    assert(lookup ~= nil and finalized == 0)
    entered = entered + 1
end

collectgarbage("collect")
assert(finalized == 1 and entered == 1)
