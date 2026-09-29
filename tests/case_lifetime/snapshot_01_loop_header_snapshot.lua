-- regress_145_loop_header_snapshot#1: loop header 必须保留调用前的 local 快照
-- unluac: expect-contains [[for ]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[7]]
local value = 1
local calls, visits = 0, 0

local function side()
    calls = calls + 1
    value = 2
    return 9
end

local start = value
local keep = side()
assert(start == 1 and keep == 9 and value == 2)
for index = start, 1 do
    assert(index == 1 and value == 2)
    visits = visits + 1
    print("loop", index)
end
assert(calls == 1 and visits == 1)
print("keep", keep)
