local function private_exit()
    local co = coroutine.create(function()
        coroutine.yield(10)
        coroutine.yield(20)
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
assert(normal_exit(0) == "public")
assert(normal_exit(2) == "1,2,public")
assert(bypass(true) == "early,public")
assert(bypass(false) == "1,nil,public")
print("loop-private-exit", private_exit(), normal_exit(0), bypass(true), bypass(false))
