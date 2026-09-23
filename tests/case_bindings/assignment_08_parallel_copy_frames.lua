-- 交换必须保持两个对象的身份，并在 repeat 回边上重新取得本轮旧值快照。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
local function swap_many(rounds)
    local left = { tag = "left" }
    local right = { tag = "right" }
    local count = 0
    repeat
        left, right = right, left
        count = count + 1
    until count >= rounds
    return left, right
end

for rounds = 1, 4 do
    local left, right = swap_many(rounds)
    assert(left ~= right)
    if rounds % 2 == 0 then
        assert(left.tag == "left" and right.tag == "right")
    else
        assert(left.tag == "right" and right.tag == "left")
    end
end
print("parallel-copy-frames", "OK")
