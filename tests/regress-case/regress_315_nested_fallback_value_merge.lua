-- regress_315_nested_fallback_value_merge: 嵌套短路的共享 fallback 值合流不能伪装 single-pass break
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[repeat]]

local hardware_type = "mobile"
local environment = {
    screenWidth = nil,
    screenHeight = nil
}
local gfx_device = {
    getViewSize = function()
        return 1920, 1080
    end
}
local viewport_width, viewport_height = 1024, 768
local window_width, window_height = viewport_width, viewport_height

if hardware_type == "mobile" then
    local env_width, env_height = environment.screenWidth, environment.screenHeight
    local width, height = env_width, env_height
    if env_width and env_height then
        width, height = env_width, env_height
    else
        if gfx_device.getViewSize then
            local device_width, device_height = gfx_device.getViewSize()
            height, width = device_height, device_width
            if width ~= 0 and height ~= 0 then
                width, height = device_width, device_height
            else
                width, height = nil, nil
            end
        end
    end
    window_width = width or viewport_width
    window_height = height or viewport_height
end

assert(window_width == 1920 and window_height == 1080)
print("regress_315_nested_fallback_value_merge", "OK")
