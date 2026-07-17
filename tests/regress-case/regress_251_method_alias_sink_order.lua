-- regress_251_method_alias_sink_order: method alias 不跨外层 callee 或循环边界

local obj = {}
local wrap

obj.m = function(self)
    return 7
end

local function method_shape_witness(value)
    return value:m()
end

local function make()
    wrap = function(value)
        return "new" .. value
    end
    return obj
end

wrap = function(value)
    return "old" .. value
end

local receiver = make()
local method = receiver.m
local result = wrap(method(receiver))
assert(result == "new7", result)

local make_count = 0
local method_count = 0
local loop_obj = {}

loop_obj.m = function(self)
    method_count = method_count + 1
    return method_count < 3
end

local function make_loop_receiver()
    make_count = make_count + 1
    return loop_obj
end

local loop_receiver = make_loop_receiver()
local loop_method = loop_receiver.m
while loop_method(loop_receiver) do
end

assert(make_count == 1, make_count)
assert(method_count == 3, method_count)
assert(type(method_shape_witness) == "function")

print("regress_251_method_alias_sink_order")
