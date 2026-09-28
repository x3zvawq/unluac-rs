-- 共享判断经纯跳转汇入同一 return；中间 connector 不应成为第三个条件出口。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-max [[if]] [[1]] [[@proto=1]]
-- 比较 RHS 的动态 key 与左侧调用在同一参数帧内，根函数只保留预期表的普通 local 声明。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=0]]

local function select_label(a, b, c)
    if a and (b or c) or not b and c then
        return "T"
    end
    return "F"
end

local expected = { "F", "T", "F", "F", "F", "T", "T", "T" }
for bits = 0, 7 do
    assert(select_label(bits >= 4, bits % 4 >= 2, bits % 2 == 1) == expected[bits + 1])
end
assert(select_label(0, false, nil) == "F")
assert(select_label("", "value", false) == "T")
assert(select_label(nil, false, {}) == "T")
assert(select_label(false, 0, true) == "F")
print("branch_shared_return_connector")
