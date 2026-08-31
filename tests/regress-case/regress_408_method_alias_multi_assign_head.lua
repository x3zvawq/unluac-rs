-- regress_408_method_alias_multi_assign_head: a pure-name assignment may consume its first RHS alias
-- unluac: expect-contains [[:m(), 9]]

local owner = {}

function owner:m()
    return 7, 99
end

local function run(source, enabled, first, second)
    if enabled then
        local receiver = source
        first, second = receiver.m(receiver), 9
    end
    return first, second
end

local first, second = run(owner, true, 0, 0)
assert(first == 7, first)
assert(second == 9, second)
print("regress_408_method_alias_multi_assign_head", first, second)
