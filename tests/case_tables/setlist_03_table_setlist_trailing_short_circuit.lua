-- regress_25_table_setlist_trailing_short_circuit#1: SETLIST 尾部多返回里的短路左值 producer 可以折回构造器
-- unluac: expect-contains [[{ tostring(]]
-- unluac: expect-contains [[background or 0]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
local function build_tags(loaded)
    local objects = {}
    if not loaded.themeLayertags then
        objects.themeLayerTags = { tostring(loaded.background or 0) }
    else
        objects.themeLayerTags = loaded.themeLayerTags
    end
    return objects.themeLayerTags[1]
end

local result = build_tags({ background = false })
assert(result == "0")
print("regress_25_table_setlist_trailing_short_circuit#1", result)

-- 数组中间的短路值属于整个构造事务，不能先恢复成独立方法帧声明。
-- unluac: expect-ast-count [[table-list-field]] [[9]]
-- unluac: expect-contains [[Settings:check("a") and "A" or false]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[Settings:check("a") and "A" or false]] [[@dialect=luau]]
local function build_selections()
    return {"one", "two", Settings:check("a") and "A" or false,
        Settings:check("b") and "B" or false, Settings:check("c") and "C" or false,
        "end1", "end2", "end3"}
end
local function check_selections()
    local previous = Settings
    for bits = 0, 7 do
        local trace = ""
        Settings = { check = function(self, key)
            assert(self == Settings)
            trace = trace .. key
            local shift = key == "a" and 1 or key == "b" and 2 or 4
            return math.floor(bits / shift) % 2 == 1
        end }
        local values = build_selections()
        assert(values[1] == "one" and values[2] == "two" and values[6] == "end1")
        assert(values[7] == "end2" and values[8] == "end3" and values[9] == nil)
        assert(values[3] == (bits % 2 == 1 and "A" or false))
        assert(values[4] == (math.floor(bits / 2) % 2 == 1 and "B" or false))
        assert(values[5] == (math.floor(bits / 4) % 2 == 1 and "C" or false))
        assert(trace == "abc")
        print("array selections", bits, values[3], values[4], values[5], trace)
    end
    Settings = previous
end
check_selections()
