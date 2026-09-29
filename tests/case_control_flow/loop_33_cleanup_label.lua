-- The numeric-for latch label follows cleanup on the continue path.
-- unluac: expect-ast-count [[close-binding]] [[2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-min [[goto]] [[1]]
local log, closed = {}, {}
local function note(value)
    log[#log + 1] = value
end
local function resource(name)
    closed[name] = false
    note("open:" .. name)
    return setmetatable({}, { __close = function()
        assert(not closed[name], name .. " closed twice")
        closed[name] = true
        note("close:" .. name)
    end })
end

local function loop_exits()
    do
        local outer <close> = resource("outer")
        for i = 1, 3 do
            do
                local inner <close> = resource("inner" .. i)
                note("body:" .. i)
                if i == 1 then goto next_iteration end
                if i == 3 then break end
            end
            assert(closed["inner" .. i] and not closed.outer)
            note("after:" .. i)
            ::next_iteration::
        end
        assert(closed.inner1 and closed.inner2 and closed.inner3 and not closed.outer)
        note("after:loop")
    end
    assert(closed.outer)
    note("done")
end

loop_exits()
local actual = table.concat(log, ",")
assert(actual == "open:outer,open:inner1,body:1,close:inner1,open:inner2,body:2,close:inner2,after:2,open:inner3,body:3,close:inner3,after:loop,close:outer,done", actual)
print("loop_cleanup_label", actual)
-- 关闭顺序已由精确 trace 观察；额外的调用准备不能越过关闭区间提升成循环状态。
-- unluac: expect-ast-count [[local-binding]] [[7]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=4]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=4]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[goto]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[call]] [[9]] [[@proto=4]]
-- unluac: expect-ast-count [[label]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[close-binding]] [[2]] [[@proto=4]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=4]]

-- 动态 key 的 CONCAT 可更新上值表；GETUPVAL 必须保留在 key 求值之后。
local function lookup_order()
    local current = { key = false }
    local replacement = { key = true }
    local key_count = 0
    local key = setmetatable({}, { __concat = function(left, right)
        assert(left == "k" and type(right) == "table")
        key_count = key_count + 1
        current = replacement
        return "key"
    end })
    local function read()
        return current["k" .. key]
    end
    assert(read() == true and key_count == 1)
end
lookup_order()
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
