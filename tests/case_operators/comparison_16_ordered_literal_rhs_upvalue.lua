-- 算术先执行左侧调用，再读取被调用更新的上值；大常量比较保留原寄存器准备。
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=3]]
local captured = 0
local calls = 0
local function update(value)
    calls = calls + 1
    captured = value
    return 1024, "extra"
end
local function append(out, value)
    out[#out + 1] = update(value) - captured > 512
end
local function at_most(value)
    return update(value) - captured <= 512
end

local out = {}
append(out, 600)
append(out, 400)
append(out, 512)
assert(#out == 3 and out[1] == false and out[2] == true and out[3] == false)
assert(calls == 3 and captured == 512)
assert(at_most(512) == true)
assert(at_most(400) == false)
assert(at_most(600) == true)
assert(calls == 6 and captured == 600)
assert(select("#", at_most(512)) == 1)
assert(calls == 7 and captured == 512)
print("ordered-literal-rhs-upvalue", out[1], out[2], out[3], calls)
