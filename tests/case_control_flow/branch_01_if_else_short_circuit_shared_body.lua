-- unluac: expect-not-contains [[(function()]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-contains [[ or ]]
-- unluac: expect-ast-min [[generic-for]] [[1]] [[@proto=2]]
-- unluac: expect-ast-min [[if]] [[2]] [[@proto=2]]
local dead_blocks = {
  one = { material = "wood" },
  two = { material = "bubble" },
  three = { material = "bossBubble" },
  four = { material = "pig", special = true },
}

local hits = {}

local function note(value)
  hits[#hits + 1] = value
end

local function remove_blocks()
  for name, block in pairs(dead_blocks) do
    if block.material == "stop" then
      return hits
    elseif block.material == "wood" then
      note("wood")
    elseif block.material == "stone" then
      note("stone")
    elseif block.material == "glass" then
      note("glass")
    elseif block.material == "bubble" or block.material == "bossBubble" then
      note("bubble")
    elseif block.material == "pig" then
      note("pig")
      if block.special then
        note(name)
      end
    else
      note("other")
    end
  end
end

remove_blocks()

-- pairs 顺序不稳定，只归一化观测结果；保留原来的遍历和分支形状。
table.sort(hits)
assert(table.concat(hits, ",") == "bubble,bubble,four,pig,wood")
print("regress_05#1", table.concat(hits, ","))
local cases = {
  { "wood", "wood" }, { "stone", "stone" }, { "glass", "glass" },
  { "bubble", "bubble" }, { "bossBubble", "bubble" },
  { "pig", "pig" }, { "unknown", "other" }, { "stop", "" },
}
for i, case in ipairs(cases) do
  dead_blocks = { one = { material = case[1] } }
  hits = {}
  local result = remove_blocks()
  assert(table.concat(hits, ",") == case[2])
  if case[1] == "stop" then assert(result == hits) else assert(result == nil) end
  print("regress_05#2", i, table.concat(hits, ","))
end
