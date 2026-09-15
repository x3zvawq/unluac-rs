-- 捕获的 nil cell 关闭后，同一寄存器的新 epoch 不能替换旧闭包的身份。
local function number_reuse()
    local saved
    do
        local value = nil
        saved = function() return value end
    end
    local reused = 17
    assert(saved() == nil)
    assert(reused == 17)
    print("number", type(saved()), reused)
end

local function function_reuse()
    local saved
    do
        local value = nil
        saved = function() return value end
    end
    local reused = function() return 23 end
    assert(saved() == nil)
    assert(reused() == 23)
    print("function", type(saved()), reused())
end

number_reuse()
function_reuse()
