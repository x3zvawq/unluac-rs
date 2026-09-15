-- regress_223_multiret_global_write_order#1: 连续全局写不能合并成逆序生效的多赋值
-- unluac: expect-not-contains [[unluac error]]
local writes = {}
local proxy = setmetatable({}, {
    __index = _G,
    __newindex = function(_, key)
        writes[#writes + 1] = key
    end,
})

local function run()
    local function pair()
        return 10, 20
    end
    local first, second = pair()
    first_global = first
    second_global = second
end

if setfenv then
    setfenv(run, proxy)
else
    debug.setupvalue(run, 1, proxy)
end
run()

assert(writes[1] == "first_global")
assert(writes[2] == "second_global")
print("regress_223_multiret_global_write_order#1", writes[1], writes[2])
