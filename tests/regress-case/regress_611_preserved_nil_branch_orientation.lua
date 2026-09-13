-- unluac: expect-contains [[if not (nil_guard_a or nil_guard_b) then]]
-- 清槽臂不能按“未读 local”删除；否定条件只交换两臂，不删除原覆盖。
local weak = setmetatable({}, {__mode = "v"})
local old = getmetatable(_G)
local take = true
local observed = 0
local function observe()
    observed = observed + 1
end
setmetatable(_G, {__index = function(_, key)
    if key == "nil_guard_a" and take then
        local value = {}
        weak[1] = value
        return value
    elseif key == "nil_guard_b" then
        return false
    elseif key == "nil_guard_print" then
        collectgarbage("collect")
        assert(weak[1] == nil)
        return observe
    end
end})
local function run()
    if nil_guard_a or nil_guard_b then
        local unused
    else
        for index = 1, 2 do end
    end
    nil_guard_print()
end
run()
take = false
run()
setmetatable(_G, old)
assert(observed == 2)
print("preserved-nil-branch", observed)
