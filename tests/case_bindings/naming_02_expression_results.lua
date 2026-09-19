-- 运算形状仅是命名提示；开放尾调用的各返回槽都取得结果提示。
-- unluac: expect-contains [[local num =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local str =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[length = #]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[ok = ]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local value =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local result, result2 =]] [[@naming-mode=heuristic]]
-- unluac: expect-not-contains [[local ok]] [[@naming-mode=simple]]
function naming_values(left, right, text)
    local product = left * right
    local joined = left .. right
    local size = #text
    local compare = left < right
    local selected = left and right
    print(product, joined, size, compare, selected)
    return product, joined, size, compare, selected
end
function naming_pair()
    return 10, 20
end
local first, second = naming_pair()
print(first, second)
assert(first == 10 and second == 20)
local p, s, n, b, v = naming_values(2, 3, "abc")
assert(p == 6 and s == "23" and n == 3 and b == true and v == 3)
