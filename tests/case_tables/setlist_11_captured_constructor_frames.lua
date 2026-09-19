-- 固定数组元素与开放尾调用共享原构造帧，完成后捕获表不改变元素的求值和宽度。
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[7]] [[@proto=1]] [[@dialect=lua5.1]]

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

local calls = 0
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
function makeOwner() return {} end
function makeValue(index) return index * 10 end
function loadValue(flag, layer, world)
    calls = calls + 1
    assert(flag and layer == 'layer' and world == 'world')
    print('load', calls)
    return { index = calls }, nil, 'tail'
end
local owner = build('layer', 'world')
assert(calls == 3)
for index = 1, 3 do
    local value, object = owner:get(index)
    assert(value == index * 10 and object.index == index)
end
local a, b, c = owner:tail()
assert(a == nil and b == 'tail' and c == nil)
print('constructor-frame', calls, b)
calls = 0
owner = build_vararg('layer', 'world', 'unused')
assert(calls == 3)
for index = 1, 3 do assert(owner:get(index).index == index) end
assert(owner:get(4) == nil and owner:get(5) == 'tail')
