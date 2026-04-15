-- common_11_runtime#1: pcall保护调用
local function test_pcall()
    local function may_fail(x)
        if x < 0 then
            error("neg:" .. x)
        end

        return x * 2
    end

    local ok1, res1 = pcall(may_fail, 2)
    local ok2, res2 = pcall(may_fail, -3)

    print("common_11_runtime#1", ok1, res1, ok2, string.match(res2, "neg:%-3") ~= nil)
end

-- common_11_runtime#2: 协程基础
local function test_coroutine()
    local co = coroutine.create(function(seed)
        local value = seed

        for step = 1, 2 do
            value = value + step
            coroutine.yield(value)
        end

        return value * 2
    end)

    local _, first = coroutine.resume(co, 10)
    local _, second = coroutine.resume(co)
    local _, third = coroutine.resume(co)

    print("common_11_runtime#2", first, second, third, coroutine.status(co))
end

-- common_11_runtime#3: xpcall错误处理
local function test_xpcall()
    local function fail()
        error("oops")
    end

    local function handler(err)
        return "handled:" .. ((string.match(err, "oops") and "oops") or err)
    end

    local ok, res = xpcall(fail, handler)
    print("common_11_runtime#3", ok, res)
end

-- common_11_runtime#4: 协程resume遮蔽
local function test_coroutine_shadow()
    local function co_test()
        local co = coroutine.create(function(a, b)
            coroutine.yield(a + b, a - b)
            return a * b
        end)

        local ok1, sum, diff = coroutine.resume(co, 10, 20)
        local ok2, product = coroutine.resume(co)

        return ok1, sum, diff, ok2, product, coroutine.status(co)
    end

    print("common_11_runtime#4", co_test())
end

-- common_11_runtime#5: xpcall处理器复用
local function test_xpcall_reuse()
    local function risky(kind)
        if kind == "ok" then
            return "safe", 12, 18
        end

        error("boom:" .. kind)
    end

    local function handler(err)
        return "handled<" .. (string.match(err, "boom:[^>]+") or err) .. ">"
    end

    local ok1, a1, b1, c1 = xpcall(function()
        return risky("ok")
    end, handler)
    local ok2, res2 = xpcall(function()
        return risky("bad")
    end, handler)

    print("common_11_runtime#5", ok1, a1, b1, c1)
    print("common_11_runtime#5", ok2, res2)
end

-- common_11_runtime#6: pcall多返回值复用
local function test_pcall_multiret()
    local function risky(flag, value)
        if flag then
            return value, value + 1, value + 2
        end

        error("bad:" .. value)
    end

    local function summarize(...)
        return table.concat({ ... }, ",")
    end

    local ok1, a1, b1, c1 = pcall(risky, true, 7)
    local ok2, err2 = pcall(risky, false, 5)

    print("common_11_runtime#6", ok1, summarize(a1, b1, c1))
    print("common_11_runtime#6", ok2, string.match(err2, "bad:5") ~= nil)
end

-- common_11_runtime#7: while-true 中 coroutine.resume 多返回值赋值 + 条件 break
local function test_coro_resume_loop()
    local function producer()
        for i = 1, 5 do
            coroutine.yield(i * 10)
        end
        return "done"
    end

    local co = coroutine.create(producer)
    local results = {}
    while true do
        local ok, val = coroutine.resume(co)
        if not ok or coroutine.status(co) == "dead" then
            results[#results + 1] = val or "nil"
            break
        end
        results[#results + 1] = val
    end
    print("common_11_runtime#7", table.concat(results, ","))
end

test_pcall()
test_coroutine()
test_xpcall()
test_coroutine_shadow()
test_xpcall_reuse()
test_pcall_multiret()
test_coro_resume_loop()
