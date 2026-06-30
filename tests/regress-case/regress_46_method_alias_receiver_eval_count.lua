-- regress_46_method_alias_receiver_eval_count#1: method alias 不能把两个相同调用 receiver 合成一次

local log = {}

local function make(tag)
    log[#log + 1] = tag
    return {
        method = function(self)
            log[#log + 1] = "method"
            return self.tag
        end,
        tag = tag,
    }
end

local receiver = make("same")
local value = make("same").method(receiver)
print("regress_46_method_alias_receiver_eval_count#1", table.concat(log, ","), value)
