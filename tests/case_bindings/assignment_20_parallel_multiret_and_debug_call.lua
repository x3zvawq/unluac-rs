-- 多返回局部接棒吸收、平行多赋值合流（含上值表字段与局部变量）及块尾具名调用局部保留。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-contains [[local BadConfig]] [[@debug=retained]]

local log = {}
local backing = { min = 5, max = 10 }
local bounds = setmetatable({}, {
    __index = backing,
    __newindex = function(_, k, v)
        log[#log + 1] = k .. "=" .. tostring(v)
        backing[k] = v
    end,
})

local function make_obj()
    return {
        getRect = function() return 10, 20, 50, 80 end,
        getPiv = function() return 2, 4 end,
        getScl = function() return 3, 5 end,
    }
end

local function compute_bounds(obj, fixture)
    local x1, y1, x2, y2
    if fixture and fixture.xmin and fixture.ymin and fixture.xmax and fixture.ymax then
        x1, y1, x2, y2 = fixture.xmin, fixture.ymin, fixture.xmax, fixture.ymax
    else
        local r1, r2, r3, r4 = obj:getRect()
        local px, py = obj:getPiv()
        local sx, sy = obj:getScl()
        x1 = (r1 - px) * sx
        y1 = (r2 - py) * sy
        x2 = (r3 - px) * sx
        y2 = (r4 - py) * sy
    end
    return x1, y1, x2, y2
end

local function update_bounds(ev, calc)
    if ev.name == "MOVED" then
        local a, b = calc(ev)
        if a ~= bounds.min or b ~= bounds.max then
            bounds.min, bounds.max = a, b
        end
    end
end

local function check_overwrite_safety()
    local t = true
    t = false
    local x = t
    assert(x == false and t == false)
    local dst = { 0 }
    local other = { 0 }
    local v = 99
    dst = other
    dst[1] = v
    assert(other[1] == 99)
end

local loaded = 0
local function load_bad_config()
    loaded = loaded + 1
    return { ok = true }
end

local function init_only()
    local BadConfig = load_bad_config()
end

local obj = make_obj()
local a1, a2, a3, a4 = compute_bounds(obj, nil)
assert(a1 == 24 and a2 == 80 and a3 == 144 and a4 == 380)
local b1, b2, b3, b4 = compute_bounds(obj, { xmin = 1, ymin = 2, xmax = 3, ymax = 4 })
assert(b1 == 1 and b2 == 2 and b3 == 3 and b4 == 4)

update_bounds({ name = "MOVED", lo = 7, hi = 12 }, function(e) return e.lo, e.hi end)
assert(bounds.min == 7 and bounds.max == 12)
update_bounds({ name = "MOVED", lo = 7, hi = 12 }, function(e) return e.lo, e.hi end)
assert(#log == 2)

check_overwrite_safety()
init_only()
assert(loaded == 1)
print("assignment_20", table.concat(log, ","), a1, a2, a3, a4, loaded)
