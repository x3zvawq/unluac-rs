-- branch-control 不得用运行不可达性删除 retain-debug 承载的源码 local 身份。
-- unluac: expect-contains [[unreachable_debug]]
-- unluac: expect-contains [[unreachable_arm]]
-- unluac: expect-contains [[while false do]]
-- unluac: expect-ast-count [[break]] [[0]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=4]]
-- unluac: expect-count [[return true]] [[1]]

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

-- 活循环的 body local 必须在下一次 header 求值前退出 debug 可见域。
local observations = {}
local function observe(where)
    local found
    for index = 1, 32 do
        local name, value = debug.getlocal(2, index)
        if name == "iteration_local" then
            found = value
        end
    end
    assert((where == "body") == (found ~= nil))
    observations[#observations + 1] = where .. ":" .. tostring(found)
    return true
end

local function live_while(limit)
    local iterations = 0
    while observe("header") and iterations < limit do
        local iteration_local = iterations + 1
        iterations = iteration_local
        observe("body")
    end
    return iterations
end

local while_result = false_while()
local if_result = false_if()
assert(while_result == 43 and if_result == 53)
assert(live_while(2) == 2)
assert(table.concat(observations, "|") == "header:nil|body:1|header:nil|body:2|header:nil")
print("regress339-debug", while_result, if_result)
