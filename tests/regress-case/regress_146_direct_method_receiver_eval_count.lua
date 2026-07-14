-- regress_146_direct_method_receiver_eval_count#1: 普通调用必须保留 receiver 的两次求值
regress_146_receiver = setmetatable({}, {
    __index = function(old)
        print("get")
        regress_146_receiver = { method = true }
        return function(self)
            print(self == old and "old" or "new")
            return 7
        end
    end,
})

local result = regress_146_receiver.method(regress_146_receiver)
print(result)
