-- 字段 GETUPVAL 的准备槽随后成为捕获 local；未来 cell 不保护此前的独立读取。
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[table-list-field]] [[6]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-record-field]] [[18]] [[@proto=2]] [[@dialect=lua5.1]]
local ease = { generation = 1 }
local trace = ""
local function curve(values)
    assert(#values == 3 and values[4] == nil)
    assert(values[1].et == ease and values[2].et == ease and values[3].et == ease)
    assert(values[1] ~= values[2] and values[2] ~= values[3])
    trace = trace .. "curve" .. ease.generation .. ";"
    ease = { generation = ease.generation + 1 }
    return values
end

local function build(anim)
    anim:setLink(1, curve({
        {t = 0, v = 0, et = ease}, {t = 0.25, v = 1, et = ease}, {t = 0.5, v = 0, et = ease},
    }), anim, 1)
    anim:setLink(2, curve({
        {t = 0, v = 0, et = ease}, {t = 0.25, v = 1, et = ease}, {t = 0.5, v = 0, et = ease},
    }), anim, 2)
    -- 第七个槽与前面字段准备重叠，必须保留实际捕获而不能用未调用的闭包作证明。
    local a, b, c, d, e, f, g = {}, {}, {}, {}, {}, {}, {}
    return function() return a, b, c, d, e, f, g end
end

local links = {}
local snapshot = build({setLink = function(self, index, values, object, field)
    assert(self == object and index == field)
    assert(values[1].et.generation == index and values[1].et ~= ease)
    assert(values[1].t == 0 and values[2].t == 0.25 and values[3].t == 0.5)
    assert(values[1].v == 0 and values[2].v == 1 and values[3].v == 0)
    links[index] = values
    trace = trace .. "link" .. index .. ";"
end})
assert(trace == "curve1;link1;curve2;link2;")
assert(links[1][1].et ~= links[2][1].et and ease.generation == 3)
local a, b, c, d, e, f, g = snapshot()
assert(a ~= b and b ~= c and c ~= d and d ~= e and e ~= f and f ~= g)
g.marker = "captured"
local again_a, _, _, _, _, _, again_g = snapshot()
assert(again_a == a and again_g == g and again_g.marker == "captured")
print("upvalue before capture", trace, ease.generation, again_g.marker)
