-- regress_409_lua55_global_merge_write_order: merging singleton declarations must not reverse writes
-- unluac: expect-order [[global first_target =]] [[global second_target =]]
-- unluac: expect-not-contains [[global first_target, second_target =]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[7]]
-- unluac: expect-ast-count [[assign]] [[2]]

local function run()
    local writes = {}
    local env = _ENV
    setmetatable(env, {
        __newindex = function(_, name, value)
            writes[#writes + 1] = name .. ":" .. value
        end,
    })

    local function mark(value)
        writes[#writes + 1] = "mark:" .. value
        return value
    end

    local first = mark(11)
    local second = mark(22)
    global first_target = first
    global second_target = second
    global<const> assert, setmetatable, table

    setmetatable(env, nil)
    local order = table.concat(writes, ",")
    assert(order == "mark:11,mark:22,first_target:11,second_target:22", order)
    return order
end

global<const> print
print("regress_409_lua55_global_merge_write_order", run())
