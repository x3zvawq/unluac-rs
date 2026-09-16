-- 短路共享 fallback 必须保留嵌套调用的开放参数、字段读取次数和单返回值。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
function edge(a)
  return GFunc and GFunc.num2 and GFunc.num2(tostring(a)) or tostring(a)
end

local conversions = 0
local calls = 0
local lookups = 0
local returned
local argument = setmetatable({}, {
  __tostring = function()
    conversions = conversions + 1
    return "value:" .. conversions
  end
})
local function convert(value)
  calls = calls + 1
  assert(value == "value:1")
  return returned, "ignored"
end
local function check(name, expected, expected_conversions, expected_calls, expected_lookups)
  conversions, calls, lookups = 0, 0, 0
  local result, extra = edge(argument)
  assert(result == expected and extra == nil, name)
  assert(conversions == expected_conversions and calls == expected_calls, name)
  assert(lookups == expected_lookups, name)
  print(name, result, conversions, calls, lookups)
end
GFunc = nil
check("missing-global", "value:1", 1, 0, 0)
GFunc = false
check("false-global", "value:1", 1, 0, 0)
GFunc = {}
check("missing-method", "value:1", 1, 0, 0)
GFunc.num2 = false
check("false-method", "value:1", 1, 0, 0)
GFunc.num2 = convert
returned = nil
check("nil-result", "value:2", 2, 1, 0)
returned = false
check("false-result", "value:2", 2, 1, 0)
returned = 0
check("zero-result", 0, 1, 1, 0)
returned = ""
check("empty-result", "", 1, 1, 0)
returned = "converted"
check("string-result", "converted", 1, 1, 0)
GFunc = setmetatable({}, {
  __index = function(_, key)
    assert(key == "num2")
    lookups = lookups + 1
    if lookups == 1 then
      return true
    end
    return convert
  end
})
check("repeated-lookup", "converted", 1, 1, 2)

-- tostring 是可替换的 global；开放参数必须保留中间 nil 和尾值，
-- 而整个 and/or 返回表达式仍只产生一个结果。
local original_tostring = tostring
tostring = function(value)
  if value ~= argument then
    return original_tostring(value)
  end
  conversions = conversions + 1
  return "value:" .. conversions, nil, "tail"
end
GFunc = { num2 = function(...)
  calls = calls + 1
  assert(select("#", ...) == 3)
  local first, hole, last = ...
  assert(first == "value:1" and hole == nil and last == "tail")
  return returned, "ignored"
end }
check("open-arguments", "converted", 1, 1, 0)
returned = false
check("open-fallback", "value:2", 2, 1, 0)
tostring = original_tostring
