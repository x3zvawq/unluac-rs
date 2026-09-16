-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- 第一项 binding 也可在内层循环重赋值，不能改变 iterator 的隐藏 control。
local function iter(_, control)
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
print("reassigned-key", seen)
