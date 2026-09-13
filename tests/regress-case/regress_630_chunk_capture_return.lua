-- 只有函数返回附带的 capture 关闭，不存在需要独立 do 的源码作用域。
-- unluac: expect-not-line [[do]]
local function pair(value)
    return value, value * value
end
local function collect(value)
    return pair(value)
end
local function summarize(value)
    local first, second = collect(value)
    assert(first == value and second == value * value)
    return first + second
end
local first, second, third = pair(3)
print("regress_630_chunk_capture_return", first, second, third, summarize(4))
