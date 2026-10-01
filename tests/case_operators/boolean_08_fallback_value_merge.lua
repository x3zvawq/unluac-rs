-- regress_315_nested_fallback_value_merge: 嵌套短路的共享 fallback 值合流不能伪装 single-pass break
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[if true then]]
-- 原 callee 的低槽前缀保留 hardware_type；比较指令本身仍须位于 assert 前。
-- unluac: expect-count [[local r0_0 = "mobile"]] [[1]]
-- unluac: expect-count [[if r0_0 == "mobile" then]] [[1]]
-- unluac: expect-order [[local r0_0 = "mobile"]] [[if r0_0 == "mobile" then]]
-- unluac: expect-order [[if r0_0 == "mobile" then]] [[assert]]
-- unluac: expect-ast-count [[function]] [[5]]
-- 原根函数保留 15 个绑定，新增路径驱动器只增加三个声明。
-- unluac: expect-ast-max [[local-binding]] [[18]] [[@proto=0]]
-- 动态路径同样保持直接 fallback，不为上值读取遗留自复制分支。
-- unluac: expect-ast-max [[local-binding]] [[8]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=3]]

local hardware_type = "mobile"
local reads = {}
local calls = 0
local environment = setmetatable({
    screenWidth = nil,
    screenHeight = nil
}, { __index = function(_, key)
    reads[#reads + 1] = key
    return nil
end })
local gfx_device = {
    getViewSize = function()
        calls = calls + 1
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
assert(calls == 1 and table.concat(reads, ",") == "screenWidth,screenHeight")
print("regress_315_nested_fallback_value_merge", "OK")

-- 保留上面的原始块布局；同一分支算法另外接收动态输入，覆盖共享 fallback 的各条路径。
local function resolve(kind)
    local window_width, window_height = viewport_width, viewport_height
    if kind == "mobile" then
        local env_width, env_height = environment.screenWidth, environment.screenHeight
        local width, height = env_width, env_height
        if env_width and env_height then
            width, height = env_width, env_height
        elseif gfx_device.getViewSize then
            local device_width, device_height = gfx_device.getViewSize()
            height, width = device_height, device_width
            if width ~= 0 and height ~= 0 then
                width, height = device_width, device_height
            else
                width, height = nil, nil
            end
        end
        window_width = width or viewport_width
        window_height = height or viewport_height
    end
    return window_width, window_height
end

local device_size = {}
gfx_device.getViewSize = function()
    calls = calls + 1
    return device_size[1], device_size[2]
end
local function check(kind, env_width, env_height, device_width, device_height,
                     expected_width, expected_height, expected_calls, expected_reads)
    environment.screenWidth, environment.screenHeight = env_width, env_height
    device_size[1], device_size[2] = device_width, device_height
    reads, calls = {}, 0
    local width, height = resolve(kind)
    assert(width == expected_width and height == expected_height)
    assert(calls == expected_calls and table.concat(reads, ",") == expected_reads)
end
check("mobile", 800, 600, 1920, 1080, 800, 600, 0, "")
check("mobile", 0, 0, 1920, 1080, 0, 0, 0, "")
check("mobile", false, 600, 1920, 1080, 1920, 1080, 1, "")
check("mobile", nil, nil, 1920, 1080, 1920, 1080, 1, "screenWidth,screenHeight")
check("mobile", nil, 600, 0, 1080, 1024, 768, 1, "screenWidth")
check("mobile", nil, nil, 1920, 0, 1024, 768, 1, "screenWidth,screenHeight")
check("mobile", nil, nil, 0, 0, 1024, 768, 1, "screenWidth,screenHeight")
check("mobile", nil, nil, false, nil, 1024, 768, 1, "screenWidth,screenHeight")
check("desktop", nil, nil, 0, 0, 1024, 768, 0, "")
gfx_device.getViewSize = nil
check("mobile", nil, 600, 1920, 1080, 1024, 600, 0, "screenWidth")
check("mobile", 800, nil, 1920, 1080, 800, 768, 0, "screenHeight")
check("mobile", false, nil, 1920, 1080, 1024, 768, 0, "screenHeight")
