-- regress_410_lua55_global_nested_callee: a temp used only as the tail callee does not escape
-- unluac: expect-contains [[global first_target, second_target =]]
-- unluac: expect-contains [[()()]]

global<const> print

local function pair()
    return 11, 22
end

local function factory()
    return pair
end

global first_target, second_target = factory()()
print("regress_410_lua55_global_nested_callee", first_target, second_target)
