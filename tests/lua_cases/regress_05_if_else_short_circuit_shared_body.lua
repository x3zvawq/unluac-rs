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

return hits