-- regress_310_open_return_captured_snapshot: open return 固定前缀保留 callee lookup 前的快照
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function run()
    local value = 1
    local calls = 0
    local proxy = setmetatable({}, {
        __index = function()
            calls = calls + 1
            value = 2
            return function()
                return 3, calls
            end
        end,
    })

    return value, proxy.tail()
end

local first, tail, calls = run()
assert(first == 1, first)
assert(tail == 3, tail)
assert(calls == 1, calls)
print("regress_310_open_return_captured_snapshot")
