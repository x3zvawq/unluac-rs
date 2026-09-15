-- regress_184_mixed_irreducible_generic_close#1: island 不能拖垮外层 generic-for、隐式 close 与 capture owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local closed = 0
local mt = {
    __close = function()
        closed = closed + 1
    end,
}

local function factory(has_item)
    local yielded = false
    local guard = setmetatable({}, mt)
    return function()
        if has_item and not yielded then
            yielded = true
            return 3
        end
    end, nil, nil, guard
end

local function run(start_left, take_left, take_right, has_item)
    local captured = 0
    local function read()
        return captured
    end

    for item in factory(has_item) do
        captured = item
        if start_left then
            goto left
        end
        goto right

        ::left::
        captured = captured + 10
        if take_left then
            goto done
        end
        goto right

        ::right::
        captured = captured + 1
        if take_right then
            goto done
        end
        goto left
    end

    ::done::
    return read()
end

local left = run(true, true, false, true)
local right = run(false, false, true, true)
local empty = run(false, false, false, false)
assert(left == 13, left)
assert(right == 4, right)
assert(empty == 0, empty)
assert(closed == 3, closed)
print("regress_184_mixed_irreducible_generic_close#1", left, right, empty, closed)
