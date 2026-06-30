-- regress_44_loop_cond_eval_order#1: loop 条件内联不能把尾部调用移到左操作数之后
-- unluac: expect-not-contains [[r0_2() == r0_1()]]
local log = {}
local value

local function side()
    log[#log + 1] = "side"
    return 1
end

local function guard()
    log[#log + 1] = "guard"
    return 1
end

repeat
    value = side()
until guard() == value

print("regress_44_loop_cond_eval_order#1", table.concat(log, ","))
