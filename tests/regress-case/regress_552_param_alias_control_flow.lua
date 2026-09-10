-- 参数 alias 消费共享 CFG：深层循环只收集一次事实，break/return 与 repeat latch 保持各自出口。
-- unluac: expect-not-contains [[unluac error]]
local function nested(value)
    for a = 1, 1 do
        for b = 1, 1 do
            for c = 1, 1 do
                for d = 1, 1 do
                    for e = 1, 1 do
                        for f = 1, 1 do
                            for g = 1, 1 do
                                for h = 1, 1 do value = value + 1 end
                            end
                        end
                    end
                end
            end
        end
    end
    return value
end

local function exits(value)
    for outer = 1, 3 do
        for inner = 1, 2 do
            value = value + 1
            if value > 20 then return value end
            if inner == 1 then break end
        end
        if outer == 2 then break end
    end
    return value
end

local function latch(value)
    repeat
        value = value + 1
        if value == 4 then break end
    until value >= 6
    return value
end

local function pretest(value)
    while value < 4 do
        value = value + 1
        if value == 2 then return value end
    end
    return value
end

assert(nested(10) == 11)
assert(exits(10) == 12)
assert(exits(20) == 21)
assert(latch(2) == 4)
assert(latch(5) == 6)
assert(pretest(0) == 2)
assert(pretest(10) == 10)
print("regress_552_param_alias_control_flow", "OK")
