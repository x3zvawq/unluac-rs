-- regress_252_materialize_preserves_eval: 等值/常量短路不能删除可观察求值
-- unluac: expect-not-contains [["logic") then]]
-- unluac: expect-not-contains [[ = r0_1("logic")]]
-- unluac: expect-not-contains [[ = r0_2("logic")]]

local trace = ""

local function mark(name)
    trace = trace .. name
    return true
end

local table_value = ({ mark("table") }) and 7 or 7
local false_value = (mark("logic") and false) or 9
local equal_value = mark("equal") and 11 or 11

assert(trace == "tablelogicequal", trace)
assert(table_value == 7, table_value)
assert(false_value == 9, false_value)
assert(equal_value == 11, equal_value)

print("regress_252_materialize_preserves_eval")
