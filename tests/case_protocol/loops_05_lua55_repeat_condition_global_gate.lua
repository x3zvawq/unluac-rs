-- Repeat body global declaration and until-condition globals remain valid under Lua 5.5 global scope.
-- unluac: expect-order [[global *]] [[print("body")]]
-- unluac: expect-contains [[global marker = 0]]
-- unluac: expect-ast-count [[repeat]] [[1]]

local function run(flag)
    global marker = 0
    global<const> assert
    repeat
        global<const> *
        print("body")
        marker = 1
    until type(flag) == "boolean"
    return marker
end

assert(run(true) == 1)
_ENV.marker = nil
assert(run(false) == 1)
