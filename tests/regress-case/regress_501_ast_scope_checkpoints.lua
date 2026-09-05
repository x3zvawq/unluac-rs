global<const> assert, print

global shared = 10
do
    global initializer_result = (function()
        shared = shared + 1
        return shared
    end)()
    global<const> shared
    assert(shared == 11)
    do
        global *
        inner_gate_value = shared + 1
    end
end
shared = 12
assert(shared == 12)

global function checkpoint_recurse(n)
    if n == 0 then return 7 end
    return checkpoint_recurse(n - 1)
end
assert(checkpoint_recurse(3) == 7)

local held = 20
do
    local held = (function() return held + 1 end)()
    local function recurse(n)
        if n == 0 then return held end
        return recurse(n - 1)
    end
    assert(recurse(2) == 21)
end
assert(held == 20)
repeat
    global<const> type
    local condition_value = shared
until type(condition_value) == "number"

local holder = {}
function holder:get()
    return shared
end
assert(holder:get() == 12)
print("ast-scope-checkpoint-boundaries", "OK")
