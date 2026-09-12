-- 原 SELF 覆盖前一调用结果；额外源码 local 会把已交给 callee 的 root 留在 caller。
-- unluac: expect-contains [[:make():next():finish()]]
local weak = setmetatable({}, {__mode = "v"})
local provider = {}
function provider:make()
    -- Outer callee must have been read before any nested method runs.
    chain_sink = function() error("callee lookup moved after arguments") end
    local item = {}
    weak.first = item
    function item:next()
        self = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.first == nil, "previous method result retained in caller")
        local last = {}
        weak.last = last
        function last:finish()
            self = nil
            collectgarbage("collect")
            collectgarbage("collect")
            assert(weak.last == nil, "last receiver retained in caller")
            return "done", nil, 17
        end
        return last
    end
    return item
end
chain_sink = function(label, a, b, c)
    assert(label == "result" and a == "done" and b == nil and c == 17)
    chain_sink = nil
    print("regress_556_method_chain_frame_roots", "OK")
end
collectgarbage("stop")
chain_sink("result", provider:make():next():finish())
