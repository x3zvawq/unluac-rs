-- 极端有限数使用紧凑指数文本；17 位输出观察每个 f64，倒数观察零的符号。
-- unluac: expect-contains [[5e-324]]
-- unluac: expect-contains [[2.2250738585072014e-308]]
-- unluac: expect-contains [[1.7976931348623157e308]]
-- unluac: expect-contains [[1e16]]
-- unluac: expect-contains [[0.000001]]
-- unluac: expect-not-contains [[000000000000000000000000000000]]

local values = {
    5e-324, -5e-324,
    2.225073858507201e-308, 2.2250738585072014e-308,
    1.7976931348623157e308, -1.7976931348623157e308,
    0.0000001, 0.000001, 0.0000010000000000000002,
    9999999999999998.0, 1e16, 1.0000000000000002e16,
    0.0, -0.0, 1.0, -2.0,
}
for index, value in ipairs(values) do
    print(index, string.format("%.17g", value), 1 / value)
    if math.type then
        assert(math.type(value) == "float")
    end
end
