-- 回编后的退出 pad 不能把已关闭资源的标签插入仍活跃的正常路径。
local log, closed
local function note(s) log[#log + 1] = s end
local function resource(name)
    closed[name] = false
    note("open:" .. name)
    return setmetatable({}, { __close = function()
        assert(closed[name] == false, name .. " closed twice")
        closed[name] = true
        note("close:" .. name)
    end })
end
local function check(name, run, expected)
    log, closed = {}, {}
    run()
    local actual = table.concat(log, ",")
    assert(actual == expected, name .. ": " .. actual)
    print(name, actual)
end

local function nested_repeat(escape)
    do
        local outer <close> = resource("outer")
        repeat
            do
                local inner <close> = resource("inner")
                note("body:inner")
                if escape then goto outside end
            end
            assert(closed.inner and not closed.outer)
            note("condition")
        until true
        note("after:repeat")
    end
    ::outside::
    assert(closed.outer and closed.inner)
    note("done")
end
check("nested_repeat_normal", function() nested_repeat(false) end,
    "open:outer,open:inner,body:inner,close:inner,condition,after:repeat,close:outer,done")
check("nested_repeat_exit", function() nested_repeat(true) end,
    "open:outer,open:inner,body:inner,close:inner,close:outer,done")

