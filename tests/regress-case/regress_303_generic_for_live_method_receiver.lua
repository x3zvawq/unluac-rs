-- regress_303_generic_for_live_method_receiver: 循环后仍存活的method receiver保留声明

local function keep_receiver(text)
    local receiver = text
    for _ in receiver:gmatch(".") do
        break
    end
    return function()
        return receiver
    end
end

print("regress_303_generic_for_live_method_receiver", keep_receiver("A")())
