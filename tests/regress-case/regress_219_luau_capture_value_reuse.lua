-- regress_219_luau_capture_value_reuse#1: CAPTURE VAL 必须与后续物理寄存器复用隔离
-- unluac: expect-not-contains [[unluac error]]
local function build(input)
    local reader

    do
        local captured = tostring(input)
        reader = function()
            return captured
        end
    end

    do
        local replacement = tostring(input + 18)
        print("replacement", replacement)
    end

    return reader
end

local reader = build(11)
assert(reader() == "11")
print("regress_219_luau_capture_value_reuse#1", reader())
