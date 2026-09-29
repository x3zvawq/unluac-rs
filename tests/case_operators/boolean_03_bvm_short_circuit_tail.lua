-- regress_12_nested_bvm_short_circuit_tail#1: nested short-circuit tail should stay structured
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[5]]
local log = {}

local function mark(tag, value)
  log[#log + 1] = tag
  return value
end

local function sample(gate, mode, metric)
  local ok

  if gate then
    ok = mark("gate", true)
  else
    local inner = mode == "direct" or mark("expensive", metric) > 10
    ok = inner
  end

  if ok then
    return "hit"
  end

  return "miss"
end

print(
  "regress_12",
  sample(false, "other", 12),
  sample(false, "other", 3),
  sample(false, "direct", 0),
  sample(true, "other", 0),
  table.concat(log, ",")
)
assert(table.concat(log, ",") == "expensive,expensive,gate")
log = {}
assert(sample(nil, "direct", false) == "hit")
assert(sample(true, "other", {}) == "hit")
assert(sample(false, "other", 10) == "miss")
assert(sample(false, "other", 11) == "hit")
assert(select("#", sample(nil, "direct", false)) == 1)
assert(table.concat(log, ",") == "gate,expensive,expensive")
