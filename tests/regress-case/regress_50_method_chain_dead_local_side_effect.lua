-- regress_50_method_chain_dead_local_side_effect#1: method-chain sugar 不能吞掉前置 dead local 的可观察初始化
-- unluac: expect-not-contains [[local r3_0 = r0_2()]]
-- unluac: expect-contains [[r0_2()]]

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

print("regress_50_method_chain_dead_local_side_effect#1", run())
