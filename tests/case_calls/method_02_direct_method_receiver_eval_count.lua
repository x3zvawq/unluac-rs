-- regress_146_direct_method_receiver_eval_count#1: 普通调用必须保留 receiver 的两次求值
-- unluac: expect-not-contains [[:method(]]
-- unluac: expect-contains [[regress_146_receiver.method(regress_146_receiver)]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-count [[return function(]] [[1]]
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
assert(result == 7)
print(result)
