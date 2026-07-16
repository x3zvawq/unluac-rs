-- regress_220_branch_close_capture_epoch#1: break cleanup 不能切断 sibling 路径的捕获写回
-- unluac: expect-not-contains [[unluac error]]
local function build(stop)
    local readers = {}
    local index = 0
    while index < 2 do
        index = index + 1
        local value
        readers[#readers + 1] = function()
            return value
        end
        if stop then
            break
        end
        value = index * 10
    end
    return readers
end

local readers = build(false)
assert(readers[1]() == 10)
assert(readers[2]() == 20)
print("regress_220_branch_close_capture_epoch#1", readers[1](), readers[2]())
