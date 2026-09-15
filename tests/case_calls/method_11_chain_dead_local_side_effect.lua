-- regress_50_method_chain_dead_local_side_effect#1: method-chain sugar 不能吞掉前置 dead local 的可观察初始化
-- 物理根的声明/赋值外形不属于本例约束；用完整事件轨迹验证调用次数与顺序。
-- unluac: expect-contains [[:step("first")]]
-- unluac: expect-contains [[:step("second")]]

local log = {}

local object = {
    step = function(self, name)
        log[#log + 1] = name
        return self
    end,
}

local function side()
    log[#log + 1] = "side"
    return "unused"
end

local function run()
    local unused = side()
    local chain = object:step("first")
    chain:step("second")
    return table.concat(log, ",")
end

local result = run()
assert(result == "side,first,second")
print("regress_50_method_chain_dead_local_side_effect#1", result)
