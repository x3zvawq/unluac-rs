-- regress_402_upvalue_function_decl: plain function syntax can assign an upvalue binding
-- unluac: expect-contains [[    function r0_0()]]
-- unluac: expect-ast-max [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=0]]

local function current()
    return 1
end

local function replace()
    current = function()
        return 7
    end
end

replace()
assert(current() == 7)
print("regress_402_upvalue_function_decl", current())
