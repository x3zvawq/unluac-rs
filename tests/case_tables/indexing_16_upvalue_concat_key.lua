-- 拼接键在原缓冲区读取上值；记录元方法改写来源时各方言原生的表读取时点。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]] [[@dialect=luau]]
-- PUC 5.4/5.5 后读的上值表也应由同一索引过程消费，不能复用键缓冲留下接棒变量。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]] [[@dialect=lua5.5]]
local events = ""
local original = setmetatable({}, {__index = function(_, key)
    events = events .. "lookup:" .. key .. ";"
    return 73
end})
local replacement = {chosen = -1}
local target = original
local prefix
prefix = setmetatable({}, {__concat = function(left, right)
    assert(left == prefix and right == "tail")
    events = events .. "concat;"
    target = replacement
    return "chosen"
end})
local function lookup(suffix)
    return target[prefix .. suffix]
end
-- GETTABUP 可在键计算后直接读取 cell；其它布局先把表读入寄存器。
-- 首次结果与查表轨迹共同参与运行比较，不能把一种方言的时点强加给其它方言。
local first = lookup("tail")
assert(target == replacement)
assert(lookup("tail") == -1)
print("upvalue concat key", first, events)
