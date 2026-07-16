-- regress_216_irreducible_linear_exit#1: island owns its single-entry observable exit chain
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run()
    local installed
    local x, y = 0, 0

    if x == 0 then
        goto left
    end
    goto right

    ::left::
    x = x + 1
    y = y + 10
    if x < 3 then
        goto right
    end

    (function()
        local function exported()
            return 42
        end
        installed = exported
    end)()
    goto done

    ::right::
    x = x + 2
    y = y + 1
    if y < 13 then
        goto left
    end

    ::done::
    print("regress_216_irreducible_linear_exit#1", x, y, installed and installed() or "skip")
end

run()
