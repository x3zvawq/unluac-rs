-- regress_405_method_alias_multi_return_head: the first value keeps its scalar return width
-- 原 GETTABLE + receiver COPY 不总能改成 SELF；语法糖许可与返回值宽度分开验证。
-- unluac: expect-contains [[, 2]]

local owner = {}

function owner:m()
    return 1, 99
end

local function run(source)
    local receiver = source
    return receiver.m(receiver), 2
end

local first, second = run(owner)
assert(first == 1, first)
assert(second == 2, second)
print("regress_405_method_alias_multi_return_head", first, second)
