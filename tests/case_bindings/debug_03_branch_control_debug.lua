-- branch-control 不得用运行不可达性删除 retain-debug 承载的源码 local 身份。
-- unluac: expect-contains [[unreachable_debug]]
-- unluac: expect-contains [[unreachable_arm]]

local function false_while()
    while false do
        local unreachable_debug = 41
        print(unreachable_debug)
    end
    return 43
end

local function false_if()
    if nil then
        local unreachable_arm = 47
        print(unreachable_arm)
    else
        return 53
    end
end

local while_result = false_while()
local if_result = false_if()
assert(while_result == 43 and if_result == 53)
print("regress339-debug", while_result, if_result)
