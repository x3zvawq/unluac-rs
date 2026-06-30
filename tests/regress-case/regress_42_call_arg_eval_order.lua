-- regress_42_call_arg_eval_order#1: call arg 内联不能越过 callee 读取
local log = {}

setmetatable(_G, {
    __index = function(_, key)
        if key == "sink" then
            log[#log + 1] = "sink"
            return function(value)
                print("regress_42_call_arg_eval_order#1", table.concat(log, ","), value)
            end
        end
    end,
})

local function source()
    log[#log + 1] = "source"
    return 42
end

local value = source()
sink(value)
