-- Sequential <close> scopes may reuse one VM register, but remain distinct resource epochs.
-- unluac: expect-contains [[<close>]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 允许内联 expected 字符串，但不增加索引、callee 或返回检查的中转声明。
-- unluac: expect-ast-max [[local-binding]] [[11]]
-- unluac: expect-ast-count [[close-binding]] [[3]]
-- unluac: expect-ast-count [[do-block]] [[2]]
-- 资源域前后复用的索引准备直接进入字段写，不留下长度中转声明。
-- unluac: expect-not-contains [[ = #]]
-- 保留比较字面量的原声明前缀，使返回检查直接调用 assert。
-- unluac: expect-count [[assert(]] [[4]]

local log = {}
local close_mt = {
    __close = function(value, err)
        assert(err == nil)
        log[#log + 1] = "close:" .. value.name
    end,
}

local function acquire(name)
    log[#log + 1] = "open:" .. name
    return setmetatable({ name = name }, close_mt)
end

do
    local first <close> = acquire("first")
    log[#log + 1] = "body:" .. first.name
end

log[#log + 1] = "between"

do
    local second <close> = acquire("second")
    log[#log + 1] = "body:" .. second.name
end

local actual = table.concat(log, ",")
local expected = "open:first,body:first,close:first,between,open:second,body:second,close:second"
assert(actual == expected, actual)

log = {}
local function return_from_r0()
    local item <close> = acquire("return")
    log[#log + 1] = "body:" .. item.name
    return item.name
end

assert(return_from_r0() == "return")
local terminal_actual = table.concat(log, ",")
local terminal_expected = "open:return,body:return,close:return"
assert(terminal_actual == terminal_expected, terminal_actual)
print("regress_334_close_scope_epochs", actual, terminal_actual)
