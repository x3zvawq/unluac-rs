-- regress_400_call_copy_only_root: a copied call result remains a root after its source home is reused

local finalized = false
local object = {}

local function make()
    return setmetatable({}, {
        __gc = function()
            finalized = true
        end,
    })
end

local function install()
    local forwarded = function()
        return 41
    end
    object.read = forwarded
    forwarded = make()
    collectgarbage("collect")
    assert(not finalized)
end

install()
collectgarbage("collect")
assert(finalized)
assert(object.read() == 41)
print("regress_400_call_copy_only_root", finalized)
