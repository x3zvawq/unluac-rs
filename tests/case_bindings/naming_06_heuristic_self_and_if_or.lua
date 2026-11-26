-- 启发式 self 方法还原（严格守住外层/内部 self 遮蔽与 debug 参数名边界）与多层互斥 if-not 展平。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-contains [[:score(]]
-- unluac: expect-contains [[.add_one(]]
-- unluac: expect-contains [[.keep_debug_name(obj]] [[@debug=retained]]

local Widget = setmetatable({}, {})

function Widget:score(bonus)
    return self.base + self:extra(bonus)
end

function Widget:extra(bonus)
    return self.scale * bonus
end

function Widget.add_one(n)
    return n + 1
end

function Widget.keep_debug_name(obj, delta)
    return obj.base + delta
end

local self = { bias = 100 }
function Widget.read_with_outer_self(item)
    return item.base + self.bias
end

local function check_any(a, b, c, d, e)
    local hit = false
    if not a then
        if not b then
            if not c then
                if not d then
                    if e then
                        hit = true
                    end
                else
                    hit = true
                end
            else
                hit = true
            end
        else
            hit = true
        end
    else
        hit = true
    end
    return hit
end

local w = setmetatable({ base = 10, scale = 3 }, { __index = Widget })
assert(w:score(4) == 22)
assert(Widget.add_one(7) == 8)
assert(Widget.keep_debug_name(w, 5) == 15)
assert(Widget.read_with_outer_self(w) == 110)

assert(check_any(true, false, false, false, false) == true)
assert(check_any(false, false, true, false, false) == true)
assert(check_any(false, false, false, false, true) == true)
assert(check_any(false, false, false, false, false) == false)

print("naming_heuristic_self_and_if_or", w:score(4), Widget.read_with_outer_self(w))
