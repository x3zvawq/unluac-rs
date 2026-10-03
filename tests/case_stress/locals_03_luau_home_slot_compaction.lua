-- regress_206_luau_home_slot_compaction#1: stripped 大函数应按 home slot 复用 local，避免源码局部槽膨胀
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[do]]
-- unluac: expect-contains [[return nil, nil]]
-- unluac: expect-not-contains [[= nil, nil]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[64]] [[@proto=2]]
-- 正常 bit32 的整条线性链最终归零；外部 fallback 另覆盖非零返回，并核对每轮快照与开放尾。
-- unluac-runtime: local run = ...
-- unluac-runtime: local original = bit32
-- unluac-runtime: for mode = 0, 1 do
-- unluac-runtime:     local step, phase, expected = 1, 1, 12345
-- unluac-runtime:     local left, right
-- unluac-runtime:     local checks, outputs, extras = 0, 0, 0
-- unluac-runtime:     local library = {
-- unluac-runtime:         lrotate = function(value, distance, ...)
-- unluac-runtime:             assert(phase == 1 and select("#", ...) == 0 and value == expected)
-- unluac-runtime:             assert(distance == (step - 1) % 31 + 1)
-- unluac-runtime:             left = original.lrotate(value, distance)
-- unluac-runtime:             phase = 2
-- unluac-runtime:             return left
-- unluac-runtime:         end,
-- unluac-runtime:         rrotate = function(value, distance, ...)
-- unluac-runtime:             assert(phase == 2 and select("#", ...) == 0 and value == expected)
-- unluac-runtime:             assert(distance == (step - 1) * 7 % 31 + 1)
-- unluac-runtime:             right = original.rrotate(value, distance)
-- unluac-runtime:             phase = 3
-- unluac-runtime:             return right, 0
-- unluac-runtime:         end,
-- unluac-runtime:         bxor = function(a, b, ...)
-- unluac-runtime:             assert(phase == 3 and a == left and b == right)
-- unluac-runtime:             local width = select("#", ...)
-- unluac-runtime:             assert(width == 0 or (width == 1 and (...) == 0))
-- unluac-runtime:             extras = extras + width
-- unluac-runtime:             expected = original.bxor(a, b)
-- unluac-runtime:             if mode == 1 and step == 64 then expected = 1 end
-- unluac-runtime:             step = step + 1
-- unluac-runtime:             phase = 1
-- unluac-runtime:             return expected
-- unluac-runtime:         end,
-- unluac-runtime:     }
-- unluac-runtime:     local function check(condition, ...)
-- unluac-runtime:         checks = checks + 1
-- unluac-runtime:         assert(select("#", ...) == 0 and condition == (mode == 0))
-- unluac-runtime:     end
-- unluac-runtime:     local function output(tag, ...)
-- unluac-runtime:         outputs = outputs + 1
-- unluac-runtime:         assert(tag == "regress_206_luau_home_slot_compaction#1" and select("#", ...) == 3)
-- unluac-runtime:         local value, marker, tail = ...
-- unluac-runtime:         if mode == 0 then
-- unluac-runtime:             assert(value == nil and marker == nil and tail == "tail")
-- unluac-runtime:         else
-- unluac-runtime:             assert(value == 1 and marker == 1 and tail == nil)
-- unluac-runtime:         end
-- unluac-runtime:     end
-- unluac-runtime:     setfenv(run, setmetatable({ bit32 = library, assert = check, print = output }, { __index = getfenv() }))
-- unluac-runtime:     run()
-- unluac-runtime:     assert(step == 65 and phase == 1 and checks == 1 and outputs == 1)
-- unluac-runtime:     assert(extras == 0 or extras == 64)
-- unluac-runtime:     print("home-slot-fallback", mode, step - 1, extras)
-- unluac-runtime: end
local function tail()
    return "tail"
end

local function churn(x)
    x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1)); x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8)); x = bit32.bxor(bit32.lrotate(x, 3), bit32.rrotate(x, 15)); x = bit32.bxor(bit32.lrotate(x, 4), bit32.rrotate(x, 22))
    x = bit32.bxor(bit32.lrotate(x, 5), bit32.rrotate(x, 29)); x = bit32.bxor(bit32.lrotate(x, 6), bit32.rrotate(x, 5)); x = bit32.bxor(bit32.lrotate(x, 7), bit32.rrotate(x, 12)); x = bit32.bxor(bit32.lrotate(x, 8), bit32.rrotate(x, 19))
    x = bit32.bxor(bit32.lrotate(x, 9), bit32.rrotate(x, 26)); x = bit32.bxor(bit32.lrotate(x, 10), bit32.rrotate(x, 2)); x = bit32.bxor(bit32.lrotate(x, 11), bit32.rrotate(x, 9)); x = bit32.bxor(bit32.lrotate(x, 12), bit32.rrotate(x, 16))
    x = bit32.bxor(bit32.lrotate(x, 13), bit32.rrotate(x, 23)); x = bit32.bxor(bit32.lrotate(x, 14), bit32.rrotate(x, 30)); x = bit32.bxor(bit32.lrotate(x, 15), bit32.rrotate(x, 6)); x = bit32.bxor(bit32.lrotate(x, 16), bit32.rrotate(x, 13))
    x = bit32.bxor(bit32.lrotate(x, 17), bit32.rrotate(x, 20)); x = bit32.bxor(bit32.lrotate(x, 18), bit32.rrotate(x, 27)); x = bit32.bxor(bit32.lrotate(x, 19), bit32.rrotate(x, 3)); x = bit32.bxor(bit32.lrotate(x, 20), bit32.rrotate(x, 10))
    x = bit32.bxor(bit32.lrotate(x, 21), bit32.rrotate(x, 17)); x = bit32.bxor(bit32.lrotate(x, 22), bit32.rrotate(x, 24)); x = bit32.bxor(bit32.lrotate(x, 23), bit32.rrotate(x, 31)); x = bit32.bxor(bit32.lrotate(x, 24), bit32.rrotate(x, 7))
    x = bit32.bxor(bit32.lrotate(x, 25), bit32.rrotate(x, 14)); x = bit32.bxor(bit32.lrotate(x, 26), bit32.rrotate(x, 21)); x = bit32.bxor(bit32.lrotate(x, 27), bit32.rrotate(x, 28)); x = bit32.bxor(bit32.lrotate(x, 28), bit32.rrotate(x, 4))
    x = bit32.bxor(bit32.lrotate(x, 29), bit32.rrotate(x, 11)); x = bit32.bxor(bit32.lrotate(x, 30), bit32.rrotate(x, 18)); x = bit32.bxor(bit32.lrotate(x, 31), bit32.rrotate(x, 25)); x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1))
    x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8)); x = bit32.bxor(bit32.lrotate(x, 3), bit32.rrotate(x, 15)); x = bit32.bxor(bit32.lrotate(x, 4), bit32.rrotate(x, 22)); x = bit32.bxor(bit32.lrotate(x, 5), bit32.rrotate(x, 29))
    x = bit32.bxor(bit32.lrotate(x, 6), bit32.rrotate(x, 5)); x = bit32.bxor(bit32.lrotate(x, 7), bit32.rrotate(x, 12)); x = bit32.bxor(bit32.lrotate(x, 8), bit32.rrotate(x, 19)); x = bit32.bxor(bit32.lrotate(x, 9), bit32.rrotate(x, 26))
    x = bit32.bxor(bit32.lrotate(x, 10), bit32.rrotate(x, 2)); x = bit32.bxor(bit32.lrotate(x, 11), bit32.rrotate(x, 9)); x = bit32.bxor(bit32.lrotate(x, 12), bit32.rrotate(x, 16)); x = bit32.bxor(bit32.lrotate(x, 13), bit32.rrotate(x, 23))
    x = bit32.bxor(bit32.lrotate(x, 14), bit32.rrotate(x, 30)); x = bit32.bxor(bit32.lrotate(x, 15), bit32.rrotate(x, 6)); x = bit32.bxor(bit32.lrotate(x, 16), bit32.rrotate(x, 13)); x = bit32.bxor(bit32.lrotate(x, 17), bit32.rrotate(x, 20))
    x = bit32.bxor(bit32.lrotate(x, 18), bit32.rrotate(x, 27)); x = bit32.bxor(bit32.lrotate(x, 19), bit32.rrotate(x, 3)); x = bit32.bxor(bit32.lrotate(x, 20), bit32.rrotate(x, 10)); x = bit32.bxor(bit32.lrotate(x, 21), bit32.rrotate(x, 17))
    x = bit32.bxor(bit32.lrotate(x, 22), bit32.rrotate(x, 24)); x = bit32.bxor(bit32.lrotate(x, 23), bit32.rrotate(x, 31)); x = bit32.bxor(bit32.lrotate(x, 24), bit32.rrotate(x, 7)); x = bit32.bxor(bit32.lrotate(x, 25), bit32.rrotate(x, 14))
    x = bit32.bxor(bit32.lrotate(x, 26), bit32.rrotate(x, 21)); x = bit32.bxor(bit32.lrotate(x, 27), bit32.rrotate(x, 28)); x = bit32.bxor(bit32.lrotate(x, 28), bit32.rrotate(x, 4)); x = bit32.bxor(bit32.lrotate(x, 29), bit32.rrotate(x, 11))
    x = bit32.bxor(bit32.lrotate(x, 30), bit32.rrotate(x, 18)); x = bit32.bxor(bit32.lrotate(x, 31), bit32.rrotate(x, 25)); x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1)); x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8))
    if x ~= 0 then
        return x, 1
    end
    return nil, nil, tail()
end

local value, marker, tail_value = churn(12345)
assert(value == nil and marker == nil and tail_value == "tail")
print("regress_206_luau_home_slot_compaction#1", value, marker, tail_value)
