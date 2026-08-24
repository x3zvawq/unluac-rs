-- regress_250_ast_inline_ordered_snapshot: binding alias 保留定义点的值快照
-- unluac: expect-not-contains [[end)(]]

local state = 1

local function mutate()
    state = 2
    return 0
end

local function take_second(_, value)
    return value
end

local function take_first(value, _)
    return value
end

local function check_param(param)
    local function mutate_param()
        param = 3
        return 0
    end

    local effect = mutate_param()
    local effect_alias = effect
    local effect_forwarded = effect_alias
    return take_first(param, effect_forwarded)
end

local snapshot = state
local alias = snapshot
local forwarded = alias
assert(take_second(mutate(), forwarded) == 1)

state = 1
local effect = mutate()
local effect_alias = effect
local effect_forwarded = effect_alias
assert(take_first(state, effect_forwarded) == 2)
assert(state == 2)
assert(check_param(1) == 3)

print("regress_250_ast_inline_ordered_snapshot")
