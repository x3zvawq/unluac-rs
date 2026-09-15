-- regress_13_if_then_merge_ownership#1: short-circuit else pad and shared tail ownership
-- unluac: expect-not-contains [[goto ]]
local log = {}

local function mark(tag, value)
  log[#log + 1] = tag
  return value
end

local function short_circuit_else_pad(a, b)
  if mark("a", a) and mark("b", b) then
    mark("good", true)
  else
    mark("bad", true)
  end

  mark("after", true)
end

local function shared_tail(a, b)
  if mark("outer", a) then
    if mark("inner", b) then
      mark("hit", true)
    end
  end

  mark("tail", true)
end

short_circuit_else_pad(false, true)
short_circuit_else_pad(true, false)
short_circuit_else_pad(true, true)
shared_tail(false, true)
shared_tail(true, false)
shared_tail(true, true)

print("regress_13", table.concat(log, ","))
