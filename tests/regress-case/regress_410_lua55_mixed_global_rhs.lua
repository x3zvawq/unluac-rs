-- regress_410_lua55_mixed_global_rhs: a fixed call is only the suffix of this declaration
-- unluac: expect-not-contains [[global second_target, third_target =]]

global<const> print

local function pair()
    return 22, 33
end

global first_target, second_target, third_target = 11, pair()
print("regress_410_lua55_mixed_global_rhs", first_target, second_target, third_target)
