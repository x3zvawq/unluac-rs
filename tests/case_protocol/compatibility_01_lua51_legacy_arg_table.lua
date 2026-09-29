-- regress_126_lua51_legacy_arg_table#1: stripped chunk 仍需恢复 Lua 5.1 固定名字的隐式 arg 表
-- unluac: expect-contains [[...]]
-- unluac: expect-contains [[arg.n]]
-- unluac: expect-not-contains [[...arg]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function(]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[3]]
local function legacy(arg, ...)
    assert(type(arg) == "table" and arg.n == 2)
    assert(arg[1] == 2 and arg[2] == 3 and arg[3] == nil)
    print("regress_126_lua51_legacy_arg_table#1", type(arg), arg.n, arg[1], arg[2])

    local calls = 0
    -- regress_126_lua51_legacy_arg_table#2: 使用 ... 后 HASARG 槽仍存在，但运行时不再填表
    local function consumed(...)
        calls = calls + 1
        assert(arg == nil and select("#", ...) == 2)
        assert(select(1, ...) == calls * 2 + 2)
        assert(select(2, ...) == calls * 2 + 3)
        print("regress_126_lua51_legacy_arg_table#2", type(arg), select("#", ...))
    end

    consumed(4, 5)
    consumed(6, 7)
    assert(calls == 2)
end

legacy(1, 2, 3)
