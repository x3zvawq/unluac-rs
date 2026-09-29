-- regress_105_luau_same_header_loop_path_owner#1: 按入口区分共享 header 的 numeric-for 与 while
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[while]] [[1]] [[@proto=1]]
local function run(a, b, xs)
    local x = 0
    repeat
        if a then
            if xs[x] then
                continue
            end
            for i = 1, 3 do
                while b do
                    x = x + 1
                end
            end
        end
        if a and b then
            break
        end
    until a
    return x
end

-- b 为假走完 numeric-for；xs[0] 为真则 continue 仍执行 until 条件。
-- b 为真且 xs[0] 为假的 while 不终止，保留结构但不运行该输入。
assert(run(true, false, {}) == 0)
assert(run(0, nil, {}) == 0)
assert(run("", false, {}) == 0)
assert(run(true, true, {[0] = 0}) == 0)
assert(run(0, true, {[0] = ""}) == 0)
local reads = 0
local xs = setmetatable({}, {__index = function(_, key)
    assert(key == 0)
    reads = reads + 1
    return false
end})
assert(run(true, false, xs) == 0 and reads == 1)
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
print("regress_105_luau_same_header_loop_path_owner#1")
