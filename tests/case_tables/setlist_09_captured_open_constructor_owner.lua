-- regress_421_captured_open_constructor_owner: captured owner keeps its LocalId after open SETLIST folding
-- unluac: expect-contains [[return function()]]
-- unluac: expect-not-contains [[table-set-list]]

local function values()
    return 10, 20, 30
end

local function build()
    local owner = { values() }
    return function()
        return owner
    end
end

local owner = build()()
assert(owner[1] == 10 and owner[2] == 20 and owner[3] == 30)
