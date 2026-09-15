-- regress_411_lua55_global_function_assignment: assignments to declared globals stay assignments
-- unluac: expect-contains [[direct_target = function()]]
-- unluac: expect-contains [[forwarded_target = function()]]
-- unluac: expect-not-contains [[global function direct_target()]]
-- unluac: expect-not-contains [[global function forwarded_target()]]

global<const> assert, print

global direct_target = 1
direct_target = function()
    return 2
end

global forwarded_target = 3
local forwarded = function()
    return 4
end
forwarded_target = forwarded

assert(direct_target() == 2)
assert(forwarded_target() == 4)
print("regress_411_lua55_global_function_assignment")
