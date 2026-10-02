-- resume 的双结果应直接声明；用成员数约束接收宽度，不绑定自动变量名。
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- co、out 与 resume 双结果共三条声明；退出分支不额外保存表尾索引。
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-count [=[out[#out + 1] = value or "nil"]=] [[2]] [[@debug=retained]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[3]]
-- unluac: expect-ast-count [[break]] [[3]]
local function private_exit(fail)
    local co = coroutine.create(function()
        coroutine.yield(10)
        coroutine.yield(20)
        if fail then error("private failure", 0) end
        return "done"
    end)
    local out = {}
    while true do
        local ok, value = coroutine.resume(co)
        if not ok or coroutine.status(co) == "dead" then
            out[#out + 1] = value or "nil"
            break
        end
        out[#out + 1] = value
    end
    return table.concat(out, ",")
end

local function normal_exit(limit)
    local index = 0
    local out = {}
    while index < limit do
        index = index + 1
        out[#out + 1] = index
    end
    -- 公共循环后缀必须在零次迭代和正常退出时都执行。
    out[#out + 1] = "public"
    return table.concat(out, ",")
end

local function bypass(early)
    local co = coroutine.create(function()
        coroutine.yield(1)
        return false
    end)
    local out = {}
    while true do
        local ok, value = coroutine.resume(co)
        if early then
            out[#out + 1] = "early"
            break
        end
        if not ok or coroutine.status(co) == "dead" then
            out[#out + 1] = value or "nil"
            break
        end
        out[#out + 1] = value
    end
    out[#out + 1] = "public"
    return table.concat(out, ",")
end

assert(private_exit() == "10,20,done")
assert(private_exit(true) == "10,20,private failure")
assert(normal_exit(-1) == "public")
assert(normal_exit(1) == "1,public")
assert(normal_exit(0) == "public")
assert(normal_exit(2) == "1,2,public")
assert(bypass(true) == "early,public")
assert(bypass(false) == "1,nil,public")
assert(bypass(nil) == "1,nil,public")
assert(bypass(0) == "early,public")
print("loop-private-exit", private_exit(), normal_exit(0), bypass(true), bypass(false))
