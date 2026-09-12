-- 共享 continuation 必须只消费一次，不能把串联菱形树化为指数个调用位置。
-- unluac: expect-contains [[("diamond-six") or ]]
local function choose(step)
    return (step("a") and (step("b") or step("c")) and step("d")) or step("e")
end

local function diamonds(step)
    return step("entry")
        and (step("left-one") or step("right-one"))
        and (step("left-two") or step("right-two"))
        and (step("left-three") or step("right-three"))
        and (step("left-four") or step("right-four"))
        and (step("left-five") or step("right-five"))
        and (step("diamond-six") or step("right-six"))
        and step("accept") or step("fallback")
end

local unexpected = 0
local object = setmetatable({}, {__eq = function()
    unexpected = unexpected + 1
    return false
end})
local options = {[1] = nil, [2] = false, [3] = true, [4] = 0, [5] = "", [6] = object}
local names = {"a", "b", "c", "d", "e"}
local function expected_choice(values)
    local expected, trace = values.a, "a"
    if expected then
        expected, trace = values.b, trace .. "b"
        if not expected then expected, trace = values.c, trace .. "c" end
        if expected then expected, trace = values.d, trace .. "d" end
    end
    if not expected then expected, trace = values.e, trace .. "e" end
    return expected, trace
end
for encoded = 0, 7775 do
    local values = {
        a = options[encoded % 6 + 1],
        b = options[math.floor(encoded / 6) % 6 + 1],
        c = options[math.floor(encoded / 36) % 6 + 1],
        d = options[math.floor(encoded / 216) % 6 + 1],
        e = options[math.floor(encoded / 1296) % 6 + 1],
    }
    local expected, trace = expected_choice(values)
    local actual_trace = ""
    local actual = choose(function(name)
        actual_trace = actual_trace .. name
        return values[name], "ignored second result"
    end)
    assert(rawequal(actual, expected) and actual_trace == trace)
end
assert(unexpected == 0)

-- 抛错必须停在原来那次调用，错误对象与此前日志均保留。
local failure = "shared short-circuit failure"
for _, stop in ipairs(names) do
    local trace = ""
    local ok, result = pcall(choose, function(name)
        trace = trace .. name
        if name == stop then error(failure, 0) end
        return name == "a" or name == "c"
    end)
    assert(not ok and rawequal(result, failure))
    local expected = {a = "a", b = "ab", c = "abc", d = "abcd", e = "abcde"}
    assert(trace == expected[stop])
end

local log = {}
assert(rawequal(diamonds(function(name)
    log[#log + 1] = name
    if name == "entry" then return true end
    if name == "accept" then return object end
    return string.sub(name, 1, 5) == "right"
end), object))
assert(table.concat(log, ",") == "entry,left-one,right-one,left-two,right-two,left-three,right-three,left-four,right-four,left-five,right-five,diamond-six,right-six,accept")
print("regress_562_shared_short_circuit", "OK")
