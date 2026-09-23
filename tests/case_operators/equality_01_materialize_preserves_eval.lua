-- regress_252_materialize_preserves_eval: 等值/常量短路不能删除可观察求值
-- unluac: expect-not-contains [["logic") then]]
-- 原 CALL 的显式 TEST 应随完整短路 initializer 保留，不能只留下裸调用和常量。
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=luajit]]
-- unluac: expect-contains [[("logic") and false or 9]] [[@dialect=lua5.5]]
-- unluac: expect-not-line [[local r0_3 = r0_1("logic")]] [[@dialect=luau]]
-- unluac: expect-contains [[{ r0_1("table") } and 7 or 7]] [[@dialect=luau]]
-- unluac: expect-contains [[r0_1("logic") and 9 or 9]] [[@dialect=luau]]
-- unluac: expect-contains [[r0_1("equal") and 11 or 11]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@dialect=luau]] [[@proto=0]]
-- unluac: expect-max-count [[("table")]] [[1]]
-- unluac: expect-max-count [[("logic")]] [[1]]
-- unluac: expect-max-count [[("equal")]] [[1]]
-- unluac: expect-contains [[assert(r0_0 == "tablelogicequal", r0_0)]] [[@dialect=luau]]
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=luau]]
-- unluac: expect-contains [[local r2_6 = -r2_2()]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@dialect=luau]] [[@proto=2]]
-- PUC/JIT 已有低槽赋值保留目标，CALL scratch 不能在再编译时阻塞后继表声明。
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[local r2_4 = r2_2() + 1]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[local r1_4 = r1_2() + 1]] [[@dialect=luajit]]

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

-- 表中的对象必须活过后继算术输入 CALL；只比较常量结果会漏掉提前覆盖暂存槽。
local function root_suffix()
    local weak = setmetatable({}, { __mode = "v" })
    local function make()
        local object = {}
        weak[1] = object
        return object
    end
    local function poll()
        for i = 1, 100000 do
            weak[2] = { i }
        end
        return weak[1] and 1 or 0
    end
    local ignored = ({ make() }) and 7 or 7
    local seen = poll() + 1
    local ignored_again = ({ make() }) and 7 or 7
    local negative = -poll()
    return ignored, seen, ignored_again, negative
end
print("conditional_root_suffix", root_suffix())
