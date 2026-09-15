-- unluac: expect-contains [[_G.type(]]
local function check(closeOnCancelKeyHandler)
    if _G.type(closeOnCancelKeyHandler) == "function" and closeOnCancelKeyHandler() then
        return true
    end

    return false
end

-- 非函数输入不得调用；函数输入只调用一次，且按 Lua 真值规则判断结果。
assert(check(nil) == false)
assert(check(false) == false)
assert(check(0) == false)
assert(check("function") == false)
local calls = 0
local result
local function handler()
    calls = calls + 1
    return result
end
assert(check(handler) == false and calls == 1)
result = false
assert(check(handler) == false and calls == 2)
result = true
assert(check(handler) == true and calls == 3)
result = 0
assert(check(handler) == true and calls == 4)
print("regress_04#1", calls, check(false))
