-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- 第一项 binding 也可在内层循环重赋值，不能改变 iterator 的隐藏 control。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
local controls = {}
local function iter(_, control)
    controls[#controls + 1] = control
    if control < 3 then
        return control + 1, 0
    end
end
local seen = 0
for key, value in iter, nil, 0 do
    for index = 1, 2 do
        key = key + 10
        value = value + key
    end
    seen = seen + value
end
assert(seen == 102)
assert(table.concat(controls, ",") == "0,1,2,3")
print("reassigned-key", seen)
