-- regress_400_call_copy_only_root: a copied call result remains a root after its source home is reused
-- 调用产生的保活值只需一个 local；不应把同槽后续 callee 留作反复改写的变量。
-- unluac: expect-ast-max [[local-binding]] [[5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-not-contains [[= collectgarbage]]
-- unluac: expect-not-contains [[= assert]]

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
