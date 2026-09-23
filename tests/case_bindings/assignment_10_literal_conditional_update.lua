-- 已有 debug local 的字面量选值不移动声明；谓词仍只执行一次，并观察赋值前的值。
-- unluac: expect-contains [[local chosen = "seed"]] [[@debug=retained]]
-- unluac: expect-contains [[chosen = test() and "one" or "two"]] [[@debug=retained]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
local function choose(flag)
    local chosen = "seed"
    local calls = 0
    local function test()
        calls = calls + 1
        assert(chosen == "seed")
        return flag
    end
    chosen = test() and "one" or "two"
    assert(calls == 1)
    return chosen
end
assert(choose(true) == "one")
assert(choose(false) == "two")
print("assignment_10_literal_conditional_update", "OK")
