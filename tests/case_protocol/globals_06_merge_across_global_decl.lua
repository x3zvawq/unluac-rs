-- regress_422_branch_merge_across_global_decl: global declarations do not erase a later arm must-def
-- unluac: expect-contains [[global branch_marker_a, branch_marker_b =]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[function]] [[2]]

global<const> assert

local function pair()
    return 10, 11
end

local function run(flag)
    local result
    if flag then
        global branch_marker_a, branch_marker_b = pair()
        result = 21
    else
        result = 22
    end
    return result
end

assert(run(false) == 22)
assert(_ENV.branch_marker_a == nil and _ENV.branch_marker_b == nil)
assert(run(true) == 21)
assert(_ENV.branch_marker_a == 10 and _ENV.branch_marker_b == 11)
assert(run(false) == 22)
