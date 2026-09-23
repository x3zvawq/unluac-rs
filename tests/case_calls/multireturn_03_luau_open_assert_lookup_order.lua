-- Luau O1/O2 FASTCALL 先求开放参数，fallback 再查找 assert；O0 普通 CALL 顺序不同。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[if]] [[0]]
local environment = getfenv(0)
local original_assert = environment.assert
local observed_tail = false
local function consume(factory)
    assert(factory())
end
consume(function()
    environment.assert = function(first, second, third)
        observed_tail = first == true and second == "tail" and third == 3
    end
    return true, "tail", 3
end)
original_assert(observed_tail)
-- 分别走每个比较的失败出口，防止合并预写时把短路结果固定成初始值或末值。
environment.assert(false, "tail", 3)
original_assert(not observed_tail)
environment.assert(true, "other", 3)
original_assert(not observed_tail)
environment.assert(true, "tail", 4)
original_assert(not observed_tail)
environment.assert(true, "tail", 3)
environment.assert = original_assert
assert(observed_tail)
print("open-assert-lookup", observed_tail)
