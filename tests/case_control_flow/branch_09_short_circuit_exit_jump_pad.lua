-- regress_34_short_circuit_exit_jump_pad#1: short-circuit 出口的空 jump pad 应随条件一起消费
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[p1_0:add("button")]] [[@dialect=lua5.1]] [[@debug=stripped]]
-- unluac: expect-contains [[:add("button")]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[12]]
-- unluac: expect-contains [[local result = maybe_add_button(state)]] [[@debug=retained]]
-- 内层仍检查 enabled；不能利用外层 not enabled 删除这次检查。
-- unluac: expect-contains [[and (p1_0.purchased or r1_0) then]] [[@dialect=lua5.1]] [[@debug=stripped]]
-- unluac: expect-not-contains [[local r1_1 = p1_0]]

local function maybe_add_button(state)
    local enabled = state.enabled
    if not enabled then
        if state.mattel and state.mattel.active then
        elseif state.powerups then
            if not state.purchased and not enabled then
            else
                state:add("button")
            end
        end
    end
    return state.count
end

local state = {
    enabled = false,
    mattel = nil,
    powerups = true,
    purchased = true,
    count = 0,
}

function state:add(_name)
    self.count = self.count + 1
end

local result = maybe_add_button(state)
assert(result == 1 and state.count == 1)
print("regress_34_short_circuit_exit_jump_pad#1", result)

-- 同时观察拒绝路径的字段访问顺序；mattel 仍要读取两次，不能合并为一次快照。
local cases = {
    {true, false, false, false, 0, "enabled,count"},
    {false, {active = true}, true, true, 0, "enabled,mattel,mattel,count"},
    {false, {active = false}, false, true, 0, "enabled,mattel,mattel,powerups,count"},
    {false, false, false, true, 0, "enabled,mattel,powerups,count"},
    {false, false, true, false, 0, "enabled,mattel,powerups,purchased,count"},
    {false, false, true, true, 1, "enabled,mattel,powerups,purchased,add,count,count"},
}
for index, case in ipairs(cases) do
    local reads = {}
    local fields = {
        enabled = case[1], mattel = case[2], powerups = case[3], purchased = case[4],
        count = 0, add = state.add,
    }
    local probe = setmetatable({}, {
        __index = function(_, key)
            reads[#reads + 1] = key
            return fields[key]
        end,
        __newindex = function(_, key, value)
            fields[key] = value
        end,
    })
    local ok, value = pcall(maybe_add_button, probe)
    assert(ok and value == case[5] and fields.count == case[5])
    assert(table.concat(reads, ",") == case[6])
    print("jump_pad_paths", index, value, table.concat(reads, ","))
end
