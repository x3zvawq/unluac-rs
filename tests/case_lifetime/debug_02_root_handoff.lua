local function check_a2(expected, level)
-- unluac: expect-contains [[local a2 = first]] [[@debug=retained]]
-- unluac: expect-order [[check_a2(false, 3)]] [[local a2 = first]] [[@debug=retained]]
-- unluac: expect-order [[local a2 = first]] [[check_a2(true, 2)]] [[@debug=retained]]
    local found = false
    local index = 1
    while true do
        local name = debug.getlocal(level, index)
        if name == nil then break end
        if name == "a2" then found = true end
        index = index + 1
    end
    assert(found == expected, expected and "a2 missing at declaration" or "a2 visible before declaration")
end
local weak = setmetatable({}, {
    __mode = "v",
    __newindex = function(target, key, value)
        check_a2(false, 3)
        rawset(target, key, value)
    end,
})
local function run()
    local first = {}
    local second = {}
    weak[1], weak[2] = first, second
    local a0 = first
    local a1 = first
    local a2 = first
    check_a2(true, 2)
    first = nil
    second = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    a0 = nil
    a1 = nil
    a2 = nil
    collectgarbage("collect")
    assert(weak[1] == nil)
end
run()
print("debug-continuation-boundary", "OK")
