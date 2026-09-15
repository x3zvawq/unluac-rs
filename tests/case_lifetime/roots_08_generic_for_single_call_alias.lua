-- regress_395_generic_for_single_call_alias: iterator 工厂的独立根必须保留到循环之后。
-- 循环体中的调用可能清空全局来源；只保留 dispatch iterator 不能替代其工厂根。

local iterator = ipairs
local values = { "one", "two" }
for index, value in iterator(values) do
    print(index, value)
end

-- unluac: expect-contains [[= ipairs]]
-- unluac: expect-not-contains [[in ipairs(]]
