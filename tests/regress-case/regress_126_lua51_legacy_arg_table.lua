-- regress_126_lua51_legacy_arg_table#1: stripped chunk 仍需恢复 Lua 5.1 固定名字的隐式 arg 表
-- unluac: expect-contains [[...]]
-- unluac: expect-contains [[arg.n]]
-- unluac: expect-not-contains [[...arg]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function(]]
local function legacy(arg, ...)
    print("regress_126_lua51_legacy_arg_table#1", type(arg), arg.n, arg[1], arg[2])

    -- regress_126_lua51_legacy_arg_table#2: 使用 ... 后 HASARG 槽仍存在，但运行时不再填表
    local function consumed(...)
        print("regress_126_lua51_legacy_arg_table#2", type(arg), select("#", ...))
    end

    consumed(4, 5)
    consumed(6, 7)
end

legacy(1, 2, 3)
