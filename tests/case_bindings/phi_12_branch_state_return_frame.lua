-- 合流转移沿用入口状态；循环子块的未物化中转不污染外层 RETURN 声明前缀。
-- unluac: expect-ast-max [[local-binding]] [[12]]
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-not-contains [[elseif p1_0 then]] [[@debug=stripped]]
-- unluac: expect-not-contains [[elseif fullscreen then]] [[@debug=retained]]
-- unluac: expect-order [[target = mode]] [[max_area = mode.w * mode.h]] [[@debug=retained]]
local function choose_mode(fullscreen, width, height, handler)
    local selected, current, modes = handler:getCurrentMode()
    local target = current
    if width and height then
        target.w = width
        target.h = height
    elseif not fullscreen then
        local max_area = 0
        for _, mode in pairs(modes) do
            if mode.w < current.w and mode.h < current.h and mode.w * mode.h > max_area then
                target = mode
                max_area = mode.w * mode.h
            end
        end
    end
    return selected, target
end

local handler = {
    getCurrentMode = function(self)
        return nil, { w = 800, h = 600, refresh = 60, bpp = 32 }, {
            { w = 640, h = 480, refresh = 60, bpp = 32 },
        }
    end,
}

local function check(fullscreen, width, height, expected_w, expected_h)
    local selected, mode = choose_mode(fullscreen, width, height, handler)
    assert(selected == nil)
    assert(mode.w == expected_w and mode.h == expected_h)
    print("branch-state", mode.w, mode.h)
end

check(false, nil, nil, 640, 480)
check(true, nil, nil, 800, 600)
check(false, 320, 240, 320, 240)
check(true, 320, 240, 320, 240)
check(false, false, 240, 640, 480)
