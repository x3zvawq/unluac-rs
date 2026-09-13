-- Luau O1/O2 FASTCALL 先求开放参数，fallback 再查找 assert；O0 普通 CALL 顺序不同。
-- unluac: expect-not-contains [[unresolved]]
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
environment.assert = original_assert
assert(observed_tail)
print("open-assert-lookup", observed_tail)
