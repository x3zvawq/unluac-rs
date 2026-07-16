-- regress_232_parent_write_after_reference_capture#1: 只读 ByReference capture 仍须观察父级后续写入
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(flag)
    local value = 1
    if flag then
        value = 2
    end

    local read = function()
        return value
    end
    value = value + 100
    return read, value
end

local read, value = run(true)
assert(read() == 102)
assert(value == 102)
print("regress_232_parent_write_after_reference_capture#1", read(), value)
