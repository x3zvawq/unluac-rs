-- regress_358_luau_fastcall_conditional: FASTCALL 参数内部的短路 RHS 仍是条件执行区域
-- unluac: expect-contains [[local r0_3 = r0_1()]]
-- unluac: expect-contains [[type(condition and r0_2(r0_3))]]
-- unluac: expect-not-contains [[type(condition and r0_2(r0_1()))]]
-- unluac: expect-not-contains [[unluac error]]

local hits = 0

local function mark()
    hits += 1
    return 41
end

local function sink(value)
    hits += 10
    return value
end

condition = false
local eager = mark()
selected = type(condition and sink(eager))

assert(hits == 1 and selected == "boolean")
print("fastcall-region", hits, selected)
