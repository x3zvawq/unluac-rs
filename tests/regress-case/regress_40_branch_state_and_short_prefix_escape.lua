-- regress_40_branch_state_and_short_prefix_escape#1: branch state 初值与短路前缀外逃值都要物化
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[local r1_3 = r1_1]]
-- unluac: expect-contains [[r1_4 = r1_9 * r1_10]]

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

local _, mode = choose_mode(false, nil, nil, handler)
print("regress_40_branch_state_and_short_prefix_escape#1", mode.w, mode.h)
