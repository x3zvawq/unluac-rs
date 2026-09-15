-- regress_40_branch_state_and_short_prefix_escape#1: branch state 初值要物化，必达字段操作数可收回
-- unluac: expect-not-contains [[unluac error]]
-- RHS 求值期间由 loop binding 保活 mode；写回后由外层 target 跨下一轮调用保活。
-- 同路径的匿名副本不再承担独有 root，无需要求它继续物化。
-- unluac: expect-contains [[local r1_3 = r1_1]]
-- 循环协议槽的保留会改变 loop binding 编号；约束同时写回两个状态，不固定 RHS 编号。
-- unluac: expect-contains [[r1_3, r1_4 =]]

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
assert(mode.w == 640 and mode.h == 480)
print("regress_40_branch_state_and_short_prefix_escape#1", mode.w, mode.h)
