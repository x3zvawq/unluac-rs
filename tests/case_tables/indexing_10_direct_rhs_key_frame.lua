-- key 求值后仍读取原低槽 RHS；目标快照时点与各 VM 的源码基线一致。
-- unluac: expect-contains [[target[key()] = value]] [[@debug=retained]]
-- unluac: expect-contains [[target[key()] = current]] [[@debug=retained]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[ = print]]
-- unluac: expect-contains [[(original[1] == marker) ~= (replacement[1] == marker)]] [[@debug=retained]]
-- unluac: expect-count [[ ~= ]] [[2]]
local target
local replacement = {}
local function append(value, key)
    target[key()] = value
    return function() end
end
local function captured(value)
    local current = value
    local function key()
        current = "changed"
        target = replacement
        return 1
    end
    target[key()] = current
    return current
end

local original = {}
local marker = {}
local calls = 0
target = original
assert(type(append(marker, function()
    calls = calls + 1
    target = replacement
    return 1
end)) == "function")
assert(calls == 1)
assert((original[1] == marker) ~= (replacement[1] == marker))
print("direct", original[1] == marker, replacement[1] == marker)

original = {}
replacement = {}
target = original
assert(captured("old") == "changed")
assert((original[1] == "changed") ~= (replacement[1] == "changed"))
print("captured", original[1], replacement[1])
