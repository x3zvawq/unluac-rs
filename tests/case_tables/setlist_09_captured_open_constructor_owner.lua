-- regress_421_captured_open_constructor_owner: captured owner keeps its LocalId after open SETLIST folding
-- unluac: expect-contains [[return function()]]
-- unluac: expect-not-contains [[table-set-list]]

-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
local mode, calls = 0, 0
local function values()
    calls = calls + 1
    if mode == 1 then return nil, false, 30 end
    if mode == 2 then return end
    return 10, 20, 30
end

local function build()
    local owner = { values() }
    return function()
        return owner
    end
end

local read = build()
local owner = read()
assert(owner[1] == 10 and owner[2] == 20 and owner[3] == 30)

assert(read() == owner and calls == 1)
owner[2] = 99
assert(read()[2] == 99)
mode = 1
local read_sparse = build()
local sparse = read_sparse()
assert(sparse[1] == nil and sparse[2] == false and sparse[3] == 30)
assert(sparse[4] == nil and read_sparse() == sparse and sparse ~= owner)
mode = 2
local read_empty = build()
local empty = read_empty()
assert(next(empty) == nil and read_empty() == empty)
assert(empty ~= sparse and empty ~= owner)
assert(read() == owner and read()[2] == 99 and read_sparse() == sparse)
assert(calls == 3)
print("captured-open-owner", calls, owner[2], sparse[2], sparse[3], next(empty))
