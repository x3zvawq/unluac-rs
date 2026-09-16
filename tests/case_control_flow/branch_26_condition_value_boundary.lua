-- 短路取值与外层条件分别拥有控制区域，字段读取保持次数与顺序。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
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
