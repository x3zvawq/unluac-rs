-- regress_43_global_arg_eval_order#1: global 参数读取不能越过 callee 读取
local log = {}

setmetatable(_G, {
    __index = function(_, key)
        if key == "source" then
            log[#log + 1] = "source"
            return 42
        end
        if key == "sink" then
            log[#log + 1] = "sink"
            return function(value)
                print("regress_43_global_arg_eval_order#1", table.concat(log, ","), value)
            end
        end
    end,
})

local value = source
sink(value)
