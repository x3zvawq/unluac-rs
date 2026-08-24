-- regress_154_lua55_generic_for_binding_scope#1: 自动关闭迭代器的物理出口不扩张for binding词法域
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[, nil, nil, ]]
-- unluac: expect-not-contains [[ = nil, nil]]
local function iter(values)
    local index = 0
    local function next_value()
        index = index + 1
        if index <= #values then
            return index, values[index]
        end
    end
    return next_value, nil, nil, setmetatable({}, { __close = function() end })
end

local out = {}
for index, value in iter({ 2, -1, 4 }) do
    if value < 0 then
        if index == 2 then
            break
        end
    else
        out[#out + 1] = value
    end
    out[#out + 1] = 7
end

print("regress_154_lua55_generic_for_binding_scope#1", table.concat(out, ","))
