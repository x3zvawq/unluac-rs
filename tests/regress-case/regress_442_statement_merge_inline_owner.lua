-- regress_442_statement_merge_inline_owner: a single-use prefix remains visible to inline-exprs
-- unluac: expect-not-contains [[local r1_0, r1_1 = p1_0, p1_1]]
-- unluac: expect-contains [[return p1_0, p1_1, p1_1]]

local function run(first, repeated)
    local once = first
    local kept = repeated
    return once, kept, kept
end

local first, second, third = run(3, 4)
assert(first == 3 and second == 4 and third == 4)
