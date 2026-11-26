-- regress_40_branch_state_and_short_prefix_escape#1: branch state 初值要物化，必达字段操作数可收回
-- RHS 求值期间由 loop binding 保活 mode；写回后由外层 target 跨下一轮调用保活。
-- 同路径的匿名副本不再承担独有 root，无需要求它继续物化。
-- 原 COPY 先更新 target，再计算面积；合流不能把已有写点拖到计算之后。

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
