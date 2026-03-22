local function co_test()
    local co = coroutine.create(function(a, b)
        coroutine.yield(a + b, a - b)
        return a * b
    end)

    local ok1, sum, diff = coroutine.resume(co, 10, 20)
    local ok2, product = coroutine.resume(co)

    return ok1, sum, diff, ok2, product, coroutine.status(co)
end

print("co-shadow", co_test())
