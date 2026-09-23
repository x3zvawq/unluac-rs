-- regress_223_multiret_global_write_order#1: 连续全局写不能合并成逆序生效的多赋值
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-count [[setmetatable({}, {]] [[2]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=0]]
-- unluac: expect-order [[first_global =]] [[second_global =]]
-- unluac: expect-contains [[assert(meta.get_owner() == replacement and reads == 1)]] [[@debug=retained]]
local writes = {}
local proxy = setmetatable({}, {
    __index = _G,
    __newindex = function(_, key, value)
        writes[#writes + 1] = key
        if key == "literal_left" or key == "separate_left" then
            assert(value == false)
        elseif key == "literal_right" or key == "separate_right" then
            assert(value == true)
        end
    end,
})

local function run()
    local function pair()
        return 10, 20
    end
    local first, second = pair()
    first_global = first
    second_global = second
    -- 并列赋值逆序提交；独立语句仍按源码顺序，二者不能互相误认。
    literal_left, literal_right = false, true
    separate_left = false
    separate_right = true
end

if setfenv then
    setfenv(run, proxy)
else
    debug.setupvalue(run, 1, proxy)
end
run()

assert(writes[1] == "first_global")
assert(writes[2] == "second_global")
assert(writes[3] == "literal_right" and writes[4] == "literal_left")
assert(writes[5] == "separate_left" and writes[6] == "separate_right")
print("regress_223_multiret_global_write_order#1", writes[1], writes[2])

-- 参数表已完成字段合并后，外层 CALL 仍须重发全局读取及闭包分配的原 scratch。
local function observe_constructor_fields()
    local original, replacement = {}, {}
    local current = original
    local reads = 0
    local function build()
        return setmetatable({}, {
            owner = FRAME_OWNER,
            get_owner = function()
                replacement = current
                return current
            end,
        })
    end
    local previous = getmetatable(_G)
    setmetatable(_G, {
        __index = function(_, key)
            assert(key == "FRAME_OWNER")
            reads = reads + 1
            current = replacement
            return original
        end,
    })
    local object = build()
    setmetatable(_G, previous)
    local meta = getmetatable(object)
    assert(meta.owner == original)
    -- CALL 会改写右侧的 captured cell，比较不能提前读取其旧值。
    replacement = original
    assert(meta.get_owner() == replacement and reads == 1)
    assert(replacement ~= original)
    print("constructor-field-order", reads)
end
observe_constructor_fields()
