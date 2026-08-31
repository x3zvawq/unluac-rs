-- regress_365_constructor_fields_other_return: folding constructor fields does not delete or rewrite an unrelated return
-- unluac: expect-contains [[get = function()]]
-- unluac: expect-not-contains [[.get = function]]

local function build(returned)
    local constructor = {}
    constructor.get = function()
        return 7
    end
    return returned
end

local marker = {}
assert(build(marker) == marker)

local function build_multi(returned)
    local constructor = {}
    constructor.get = function()
        return 9
    end
    return returned, constructor
end

local returned, constructor = build_multi(marker)
assert(returned == marker and constructor.get() == 9)
