-- regress_367_repeat_nested_close_owner: a nested loop closes its resources before the outer repeat tail
-- unluac: expect-contains [[until mark("stop", true) or mark("again", false)]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
-- unluac: expect-ast-count [[close-binding]] [[2]]
-- unluac: expect-ast-count [[repeat]] [[2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-count [[break]] [[0]]

local events = {}

local close_meta = {
    __close = function(value)
        events[#events + 1] = "close:" .. value.label
    end,
}

function mark(name, value)
    events[#events + 1] = name
    return value
end

repeat
    for index = 1, 1 do
        local resource <close> = setmetatable({ label = index }, close_meta)
        events[#events + 1] = "body:" .. resource.label
    end
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "body:1,close:1,stop")

-- 内层两次关闭先于外层两个 guard；首次 until 为假，第二轮才退出。
events = {}
repeat
    for index = 1, 2 do
        local resource <close> = setmetatable({ label = index }, close_meta)
        events[#events + 1] = "body:" .. resource.label
    end
    if mark("stop", false) then
        break
    end
until mark("again", #events >= 11)
assert(table.concat(events, ",") ==
    "body:1,close:1,body:2,close:2,stop,again,body:1,close:1,body:2,close:2,stop,again")
