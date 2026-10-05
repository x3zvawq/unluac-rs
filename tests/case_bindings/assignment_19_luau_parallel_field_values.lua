-- 两个 RHS 先完成求值，再按 Luau 正序发布；调用与分配共用同一赋值帧。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=0]]
local events = ""
local sink = setmetatable({}, {__newindex = function(self, key, value)
    events = events .. key .. ";"
    rawset(self, key, value)
end})
local function make(tag)
    events = events .. tag .. ";"
    return {tag = tag}
end
sink.first, sink.second = make("A"), make("B")
sink.third, sink.fourth = {}, {}
sink.fifth, sink.sixth = "literal", make("C")
assert(sink.first.tag == "A")
assert(sink.second.tag == "B")
assert(sink.third ~= sink.fourth)
assert(next(sink.third) == nil)
assert(next(sink.fourth) == nil)
assert(sink.fifth == "literal")
assert(sink.sixth.tag == "C")
assert(events == "A;B;first;second;third;fourth;C;fifth;sixth;")
print("luau parallel field values", events)
