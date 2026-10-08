-- 前次分配复用槽位后，备用空表仍留在短路分支内，后续构造不留下接棒变量。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-contains [[CompassProbe = CompassProbe or {}]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[CompassProbe.effects = {]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[CompassProbe.help = {]] [[@dialect=lua5.1]]
local function build()
    HoroPrefix = {}
    CompassProbe = CompassProbe or {}
    CompassProbe.effects = {
        [0] = { condition = function(a, b) return false, 0 end, text = "pending" },
        [1] = { text = "normal", help = "description" },
        [2] = {
            condition = function(a, b) return math.floor(b / 5) > 0, math.floor(b / 5), 0 end,
            text = "active", help = "first" .. "second",
        },
        [3] = {},
    }
    CompassProbe.help = { state = "one" .. "two" .. "three", info = "four" .. "five" }
end

CompassProbe = nil
build()
local first = CompassProbe
assert(CompassProbe.effects[0].condition(0, 8) == false)
local enabled, count, extra = CompassProbe.effects[2].condition(0, 12)
assert(enabled and count == 2 and extra == 0)
assert(CompassProbe.effects[2].help == "firstsecond")
assert(CompassProbe.help.state == "onetwothree" and CompassProbe.help.info == "fourfive")
CompassProbe.marker = "kept"
build()
assert(CompassProbe == first and CompassProbe.marker == "kept")
CompassProbe = false
build()
assert(type(CompassProbe) == "table" and CompassProbe ~= first and CompassProbe.marker == nil)
assert(CompassProbe.effects[1].text == "normal" and next(CompassProbe.effects[3]) == nil)
print("compass branches", enabled, count, extra, CompassProbe.help.state)
