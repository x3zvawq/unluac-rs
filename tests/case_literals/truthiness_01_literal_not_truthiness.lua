-- alias 清理可以内联常量，但不能删除字节码中的 NOT；Luau 已在编译时折叠此操作。
-- unluac: expect-contains [[return not 7]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[return not 7]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[return not 7]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[return not 7]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[return not 7]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[return not 7]] [[@dialect=luajit]]
-- unluac: expect-contains [[return false]] [[@dialect=luau]]

local function folded_literal_not()
    local value = 7
    return not value
end

assert(folded_literal_not() == false)
print("regress_439_literal_not_truthiness", "OK")
