global none, print
global counter, label = 9, "seed"

global function step(delta)
    counter = counter * 2 + delta
    return label .. ":" .. counter
end

local first = step(3)
local second = step(5)

print("g55-basic", first, second, counter, label)
