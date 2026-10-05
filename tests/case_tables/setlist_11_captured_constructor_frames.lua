-- 固定数组元素与开放尾调用共享原构造帧，完成后捕获表不改变元素的求值和宽度。
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[7]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[20]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[27]]
-- unluac: expect-ast-count [[function]] [[12]]
-- unluac: expect-ast-count [[table-constructor]] [[5]]
-- unluac: expect-ast-count [[table-list-field]] [[10]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[empty-local]] [[0]]

local function build(layer, world)
    local owner = makeOwner()
    local constructors = {
        function() return makeValue(1) end,
        function() return makeValue(2) end,
        function() return makeValue(3) end,
        function() return makeValue(4) end,
    }
    local objects = {
        loadValue(true, layer, world),
        loadValue(true, layer, world),
        loadValue(true, layer, world)
    }
    function owner:get(index) return constructors[index](), objects[index] end
    function owner:tail() return objects[4], objects[5], objects[6] end
    return owner
end

local calls, owner_calls, value_calls = 0, 0, 0
local function build_vararg(...)
    local layer, world = ...
    local owner = makeOwner()
    local objects = {
        loadValue(true, layer, world),
        loadValue(true, layer, world),
        loadValue(true, layer, world)
    }
    function owner:get(index) return objects[index] end
    return owner
end
function makeOwner()
    owner_calls = owner_calls + 1
    return {}
end
function makeValue(index)
    value_calls = value_calls + 1
    return index * 10, "extra"
end
function loadValue(flag, layer, world)
    calls = calls + 1
    assert(flag and layer == 'layer' and world == 'world')
    print('load', calls)
    return { index = calls }, nil, 'tail'
end
local owner = build('layer', 'world')
assert(calls == 3 and owner_calls == 1 and value_calls == 0)
for index = 1, 3 do
    local value, object = owner:get(index)
    assert(value == index * 10 and object.index == index)
end
local fourth, missing = owner:get(4)
assert(fourth == 40 and missing == nil and value_calls == 4)
assert(select("#", owner:get(1)) == 2 and value_calls == 5)
local a, b, c = owner:tail()
assert(a == nil and b == 'tail' and c == nil)
assert(select("#", owner:tail()) == 3)
print('constructor-frame', calls, b)
calls = 0
local original_owner = owner
owner = build_vararg('layer', 'world', 'unused')
assert(calls == 3 and owner_calls == 2 and owner ~= original_owner)
for index = 1, 3 do assert(owner:get(index).index == index) end
assert(owner:get(4) == nil and owner:get(5) == 'tail')
assert(select("#", owner:get(4)) == 1)
assert(owner:get(6) == nil)
local _, original_object = original_owner:get(1)
assert(value_calls == 6 and original_object ~= owner:get(1))
original_object.index = 99
local _, repeated_object = original_owner:get(1)
assert(value_calls == 7 and repeated_object == original_object and repeated_object.index == 99)
assert(owner:get(1).index == 1 and calls == 3)
