-- 条件输入的原低槽仍属于分支内多返回 CALL 的前缀；空接收声明不能截断该事实。
local enabled = true
local calls = 0
local seen = 0
function probe()
    calls = calls + 1
    return enabled
end
function pair()
    calls = calls + 1
    return "left", "right"
end
function accept(values)
    assert(values[1] == "left" and values[2] == "right" and #values == 2)
    seen = seen + 1
end
function show()
    local name = probe()
    if name then
        local x, y = pair()
        accept({x, y})
    end
end
show()
assert(calls == 2 and seen == 1)
enabled = false
show()
assert(calls == 3 and seen == 1)
print("branch-multi-result-prefix", calls, seen)
