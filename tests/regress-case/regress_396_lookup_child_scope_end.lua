-- regress_396_lookup_child_scope_end: child lookup root ends at the proven home reuse boundary

local finalized = 0
local mt = {
    __gc = function()
        finalized = finalized + 1
    end,
}
local weak = setmetatable({}, { __mode = "v" })
local owner = setmetatable({}, mt)
weak.value = owner
owner = nil

if finalized == 0 then
    local lookup = weak.value
    collectgarbage("collect")
    assert(lookup ~= nil)
end

collectgarbage("collect")
assert(finalized == 1)
