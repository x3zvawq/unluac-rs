-- 折叠 `if [not] C then x = E or D else x = D end` 为无 falsy 陷阱的 `C and E or D`，
-- 并保持短路调用单值返回宽度、求值次数与 NaN 比较语义。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-not-contains [[else]]

local calls = {}

local function fallback_str(a)
    calls[#calls + 1] = "fb:" .. tostring(a)
    return "FB:" .. tostring(a)
end

local GFunc = nil

local function edge(a)
    return GFunc and GFunc.num2 and GFunc.num2(fallback_str(a)) or fallback_str(a)
end

local function pair()
    return "first", "second"
end

local function single_or(flag)
    return flag or pair()
end

local function nan_guarded(x, y, e)
    local out
    if x < y then
        out = fallback_str(x)
    else
        out = e or fallback_str(x)
    end
    return out
end

-- 1. GFunc == nil：只调用一次 fallback_str
calls = {}
assert(edge(1) == "FB:1")
assert(table.concat(calls, ",") == "fb:1")

-- 2. GFunc.num2 == nil：只调用一次 fallback_str
GFunc = {}
calls = {}
assert(edge(2) == "FB:2")
assert(table.concat(calls, ",") == "fb:2")

-- 3. GFunc.num2 返回真值：不触发右侧 fallback
GFunc = {
    num2 = function(s)
        calls[#calls + 1] = "num2:" .. s
        return "OK:" .. s
    end,
}
calls = {}
assert(edge(3) == "OK:FB:3")
assert(table.concat(calls, ",") == "fb:3,num2:FB:3")

-- 4. GFunc.num2 返回 false / nil（falsy）：必须回退到右侧 fallback（精确调用两次）
GFunc.num2 = function(s)
    calls[#calls + 1] = "false:" .. s
    return false
end
calls = {}
assert(edge(4) == "FB:4")
assert(table.concat(calls, ",") == "fb:4,false:FB:4,fb:4")

GFunc.num2 = function(s)
    calls[#calls + 1] = "nil:" .. s
    return nil
end
calls = {}
assert(edge(5) == "FB:5")
assert(table.concat(calls, ",") == "fb:5,nil:FB:5,fb:5")

-- 5. 短路返回单值截断：pair() 返回两值但 `flag or pair()` 只能返回 1 个值
assert(select("#", single_or(false)) == 1 and single_or(false) == "first")
assert(select("#", single_or("kept")) == 1 and single_or("kept") == "kept")

-- 6. NaN 比较安全：`nan < 1` 为 false，走 else 分支
local nan = 0 / 0
assert(nan_guarded(nan, 1, "hit") == "hit")
assert(nan_guarded(nan, 1, false) == "FB:" .. tostring(nan))
assert(nan_guarded(0, 1, "hit") == "FB:0")

print("folding_03_guarded_or_fallback_return", "OK")
