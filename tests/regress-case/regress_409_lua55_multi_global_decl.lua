-- regress_409_lua55_global_merge_write_order: merging singleton declarations must not reverse writes
-- unluac: expect-order [[global first_target =]] [[global second_target =]]
-- unluac: expect-not-contains [[global first_target, second_target =]]

local function run()
    local writes = {}
    local env = _ENV
    setmetatable(env, {
        __newindex = function(_, name)
            writes[#writes + 1] = name
        end,
    })

    local function mark(value)
        return value
    end

    local first = mark(11)
    local second = mark(22)
    global first_target = first
    global second_target = second
    global<const> assert, setmetatable, table

    setmetatable(env, nil)
    local order = table.concat(writes, ",")
    assert(order == "first_target,second_target", order)
    return order
end

global<const> print
print("regress_409_lua55_global_merge_write_order", run())
