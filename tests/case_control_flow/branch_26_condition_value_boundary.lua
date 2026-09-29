-- 短路取值与外层条件分别拥有控制区域，字段读取保持次数与顺序。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- 两次索引沿原 GETUPVAL 准备帧树化，不为只用一次的 base/key 留下载体。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]]
local calls = 0
local trace = {}
local rows = {
  [2] = { num2 = 5 },
  [3] = { num1 = false, num2 = 5 },
  [4] = { num1 = 0, num2 = 5 },
  [5] = { num1 = 2, num2 = 3 },
  [6] = { num1 = 2, num2 = 4 },
  [7] = { num1 = -1, num2 = 6 },
  [8] = { num1 = 10, num2 = -4 },
  [9] = { num1 = 1, num2 = 3 },
}
taskById = function(i)
  calls = calls + 1
  assert(i == calls)
  local kind = i % 10
  if kind == 0 then return nil end
  if kind == 1 then return false end
  local reads = 0
  return setmetatable({}, { __index = function(_, key)
    reads = reads + 1
    assert((reads == 1 and key == "num1") or (reads == 2 and key == "num2"))
    trace[#trace + 1] = i .. ":" .. key
    return rows[kind][key]
  end }), "ignored"
end

local x = 0
for i = 1, 100 do
  local task = taskById(i)
  if task then
    local n1 = task.num1 or 0
    if n1 + task.num2 <= 5 then
      x = x + 1
    end
  end
end

assert(x == 60)
print("matched", x)
assert(calls == 100 and #trace == 160)
print("calls", calls, "reads", #trace)
print(table.concat(trace, ","))

-- 第一层索引可改变第二层键：同名上值的两次 GETUPVAL 不是同一个值版本。
local selected, catalog = 1, nil
local function lookup()
  return catalog[selected][selected]
end
local lookup_trace = ""
catalog = setmetatable({}, { __index = function(_, key)
  assert(key == 1)
  lookup_trace = lookup_trace .. "outer"
  selected, catalog = 2, {}
  return setmetatable({}, { __index = function(_, inner_key)
    assert(inner_key == 2)
    lookup_trace = lookup_trace .. ",inner"
    return 42
  end })
end })
assert(lookup() == 42 and lookup_trace == "outer,inner")
print("upvalue lookup order", lookup_trace)
