-- regress_217_terminal_close_capture_epoch#1: 终结分支的 close 不得切断旁路上的共享 capture
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function build(skip_write)
    local value
    local read = function()
        return value
    end

    if skip_write then
        return read
    end

    value = 1
    local write = function()
        value = 2
    end
    return read, write
end

local read, write = build(false)
assert(read() == 1)
write()
assert(read() == 2)
print("regress_217_terminal_close_capture_epoch#1", "OK")
