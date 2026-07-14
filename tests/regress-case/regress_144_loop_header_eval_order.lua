-- regress_144_loop_header_eval_order#1: loop header 内联不得跨过副作用重排元方法运算
-- unluac: expect-contains [[for ]]
local mt = {
    __add = function(value)
        print("add", value.tag)
        return value.value
    end,
}

local function make(tag)
    print("make", tag)
    return setmetatable({ tag = tag, value = 1 }, mt)
end

local function side()
    print("side")
    return 9
end

local start = make("start") + 0
local keep = side()
local limit = make("limit") + 0
local step = make("step") + 0
for value = start, limit, step do
    print("loop", value)
end
print("keep", keep)
