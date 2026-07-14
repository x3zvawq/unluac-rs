-- regress_145_loop_header_snapshot#1: loop header 必须保留调用前的 local 快照
-- unluac: expect-contains [[for ]]
local value = 1

local function side()
    value = 2
    return 9
end

local start = value
local keep = side()
for index = start, 1 do
    print("loop", index)
end
print("keep", keep)
