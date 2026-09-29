-- 比较参数在原 scratch 求算术值；索引先于 RHS，元方法不能令赋值 key 后移。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[7]]
local function update(out, value, emit)
    out[#out + 1] = emit(value % 2 == 0)
end

local mod_calls, emit_calls = 0, 0
local remainder = 0
local out = { "first" }
local value = setmetatable({}, {
    __mod = function(_, divisor)
        assert(divisor == 2)
        mod_calls = mod_calls + 1
        assert(emit_calls == 0)
        out[2] = "during"
        return remainder
    end,
})
local function emit(flag)
    assert(type(flag) == "boolean")
    emit_calls = emit_calls + 1
    assert(mod_calls == 1)
    return flag and "even" or "odd", "extra"
end

update(out, value, emit)
assert(#out == 2 and out[2] == "even")
update(out, 3, emit)
assert(#out == 3 and out[3] == "odd")
assert(mod_calls == 1 and emit_calls == 2)
print("arithmetic-argument", table.concat(out, "|"), mod_calls, emit_calls)
-- 索引赋值只能接收回调的第一个结果，第二个结果不能写入相邻元素。
update(out, 4, emit)
update(out, -3, emit)
assert(#out == 5 and out[4] == "even" and out[5] == "odd")
assert(mod_calls == 1 and emit_calls == 4)
mod_calls, emit_calls = 0, 0
remainder = 1
out = { "first" }
update(out, value, emit)
assert(#out == 2 and out[2] == "odd" and mod_calls == 1 and emit_calls == 1)
assert(select("#", update(out, 2, emit)) == 0)
assert(#out == 3 and out[3] == "even" and mod_calls == 1 and emit_calls == 2)
mod_calls, emit_calls = 0, 0
remainder = 0 / 0
out = { "first" }
update(out, value, emit)
assert(#out == 2 and out[2] == "odd" and mod_calls == 1 and emit_calls == 1)
mod_calls, emit_calls = 0, 0
remainder = nil
out = { "first" }
update(out, value, emit)
assert(#out == 2 and out[2] == "odd" and mod_calls == 1 and emit_calls == 1)
