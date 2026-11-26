-- 空循环仍有源码变量身份；零长度 debug 区间属于 iterator 的结果而非入口旧槽。
-- unluac: expect-ast-count [[generic-for]] [[2]]
local calls = 0
local function run()
    local function iterate(state, control)
        calls = calls + 1
        if control < 3 then
            return control + 1, "payload"
        end
    end
    for entry, payload in iterate, nil, 0 do
    end
    for _ in iterate, nil, 0 do
    end
end
run()
assert(calls == 8)
print("empty-generic-for-bindings", calls)
