-- regress_395_generic_for_single_call_alias: a recovered iterator callee alias is safe to inline

local iterator = ipairs
local values = { "one", "two" }
for index, value in iterator(values) do
    print(index, value)
end

-- unluac: expect-contains [[in ipairs(]]
-- unluac: expect-not-contains [[local iterator = ipairs]]
