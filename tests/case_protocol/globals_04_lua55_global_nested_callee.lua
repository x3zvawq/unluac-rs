-- regress_410_lua55_global_nested_callee: a temp used only as the tail callee does not escape
-- unluac: expect-contains [[global first_target, second_target =]]
-- unluac: expect-contains [[()()]]
-- unluac: expect-contains [[global left_target, right_target =]]
-- unluac: expect-contains [[global single_target =]]
-- unluac: expect-count [[()()]] [[5]]
-- unluac: expect-count [[local _ENV =]] [[2]]
-- unluac: expect-count [[global left_target, right_target =]] [[3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=10]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=11]]

global<const> print, collectgarbage, getmetatable, setmetatable, rawset, pcall, table, assert

local function pair()
    return 11, 22
end

local function factory()
    return pair
end

global first_target, second_target = factory()()
global single_target = factory()()
assert(first_target == 11 and second_target == 22 and single_target == 11)
print("regress_410_lua55_global_nested_callee", first_target, second_target)

local function observe(occupied, mode)
    local collect = collectgarbage
    local weak = setmetatable({}, { __mode = "v" })
    local events = {}
    local function record(message)
        events[#events + 1] = message
    end
    local function pair()
        record("pair")
        local left, right = {}, {}
        weak[1], weak[2] = left, right
        return left, right
    end
    local function factory()
        record("factory")
        return pair
    end
    local env = mode == 1 and _ENV or {}
    local previous_meta = getmetatable(env)
    setmetatable(env, {
        __index = function(_, name)
            collect("collect")
            record("probe:" .. name .. ":" .. (weak[1] and "1" or "0") .. (weak[2] and "1" or "0"))
        end,
        __newindex = function(_, name, value)
            -- 不存入 env，避免环境的强引用掩盖原调用/结果槽的存活差异。
            record("store:" .. name .. ":" .. (value == weak[1] and "left" or "right"))
        end,
    })
    if occupied then
        rawset(env, occupied, true)
    end
    local function initialize()
        global left_target, right_target = factory()()
    end
    local function initialize_local()
        -- 同一协议在独立表的词法环境中运行，不能误认作根环境的 upvalue cell。
        local _ENV = env
        global left_target, right_target = factory()()
    end
    local function initialize_parameter(unused, environment)
        -- 参数与环境快照保留独立槽，不能把参数本身改名为词法环境。
        local _ENV = environment
        global left_target, right_target = factory()()
    end
    local ok
    if mode == 3 then
        ok = pcall(initialize_parameter, false, env)
    else
        ok = pcall(mode == 2 and initialize_local or initialize)
    end
    setmetatable(env, previous_meta)
    if occupied then
        rawset(env, occupied, nil)
    end
    return ok, table.concat(events, ",")
end

for mode = 1, 3 do
    local ok, events = observe(nil, mode)
    assert(ok)
    assert(events == "factory,pair,probe:right_target:11,store:right_target:right,probe:left_target:11,store:left_target:left", events)
    local right_ok, right_events = observe("right_target", mode)
    assert(not right_ok and right_events == "factory,pair", right_events)
    local left_ok, left_events = observe("left_target", mode)
    assert(not left_ok and left_events == "factory,pair,probe:right_target:11,store:right_target:right", left_events)
    print("global_nested_protocol", events, right_events, left_events)
end
