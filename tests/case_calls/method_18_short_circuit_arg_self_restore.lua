-- 短路参数跨块冲刷后的三行 SELF 还原为方法调用，
-- 表写入短路右值与取反布尔分支保持干净表达式与精确求值顺序。
-- unluac: expect-ast-min [[method-call]] [[3]]
-- unluac: expect-contains [[:show(]]
-- unluac: expect-contains [[:compute(]]

local log = {}
local cache = {}
local last_flag = nil

local function make_widget(tag)
    local w = { tag = tag }
    function w:show(v)
        log[#log + 1] = self.tag .. ":" .. tostring(v)
    end
    function w:compute(v)
        return self.tag .. "=" .. tostring(v)
    end
    return w
end

local function fetch(k)
    if k == "hit" then
        return 42
    end
    return nil
end

local function exercise(w, a, b, key, score)
    w:show(a and b)
    local out = w:compute(a or b)
    cache[key] = fetch(key) or 0
    if 0 < score then
        last_flag = false
    else
        last_flag = true
    end
    return out, w:compute(a and b or "none")
end

local w1 = make_widget("W")
local r1, r2 = exercise(w1, true, 7, "hit", 5)
assert(r1 == "W=true" and r2 == "W=7")
assert(cache.hit == 42 and last_flag == false)

local r3, r4 = exercise(w1, false, "alt", "miss", 0)
assert(r3 == "W=alt" and r4 == "W=none")
assert(cache.miss == 0 and last_flag == true)

assert(#log == 2 and log[1] == "W:7" and log[2] == "W:false")
print("method_18_short_circuit_arg_self_restore", r1, r2, r3, r4)
