-- regress_218_parent_write_terminal_capture#1: 终结 close 不得让父级后续写入脱离只读 capture
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
    return read
end

local read = build(false)
assert(read() == 1)
print("regress_218_parent_write_terminal_capture#1", "OK")
