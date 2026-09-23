-- regress_338_locals_value_flow: locals promotion 不能吞掉循环头状态或首次写前读取
-- unluac: expect-contains [[r1_0 = false]]
-- unluac: expect-contains [[if r2_0 then]]
-- 条件必须读取 repeat 体内有初始化的同一 binding，不依赖其它保留槽造成的命名偏移。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=0]]
-- repeat 的入口状态与回边共用身份，返回前不另建只转交数值的 local。
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=3]]
-- unluac: expect-not-contains [[= r0_4(true)]]
-- unluac: expect-not-contains [[= r0_5(true)]]
-- unluac: expect-not-contains [[unluac error]]

local function loop_alias(value)
    local state = value
    local observed
    while state do
        local next_value = false
        state = next_value
        observed = state
    end
    return observed
end

local function branch_condition(value)
    local state = value
    local observed
    local count = 0
    while state and count < 1 do
        if state then
            state = 11
        else
            state = 22
        end
        observed = state
        count = count + 1
    end
    return observed
end

local function repeat_condition()
    local count = 0
    local observed
    repeat
        local done = count >= 1
        observed = done
        count = count + 1
    until done
    return observed, count
end

local alias_observed = loop_alias(true)
local branch_observed = branch_condition(true)
local repeat_observed, repeat_count = repeat_condition()
assert(alias_observed == false)
assert(branch_observed == 11)
assert(repeat_observed == true and repeat_count == 2)
print(
    "regress_338_locals_value_flow",
    alias_observed,
    branch_observed,
    repeat_observed,
    repeat_count
)
