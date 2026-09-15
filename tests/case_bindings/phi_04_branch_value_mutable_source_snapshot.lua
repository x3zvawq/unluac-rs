-- regress_267_branch_value_mutable_source_snapshot: branch value必须读取臂内改写后的loop local
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unluac error]]
local function run(flag)
    local total = 0
    for i = 1, 1 do
        local value
        if flag then
            i = 10
            value = i
        else
            i = 20
            value = i
        end
        total = total + i * 100 + value
    end
    return total
end

local function direct_write()
    local value
    for i = 1, 1 do
        i = 30
        value = i
    end
    return value
end

local function generic_write()
    local result
    for key, value in ipairs({ 0 }) do
        key = 40
        value = 50
        result = key * 100 + value
    end
    return result
end

assert(run(true) == 1010)
assert(run(false) == 2020)
assert(direct_write() == 30)
assert(generic_write() == 4050)
print(
    "regress_267_branch_value_mutable_source_snapshot",
    run(true),
    run(false),
    direct_write(),
    generic_write()
)
