-- regress_288_luau_shared_proto_dag: O2复用的flat proto必须展开到每个词法child slot
-- unluac: expect-contains [[function]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function outer(z)
    local function make(a)
        return function(x)
            return a + x + z
        end
    end
    return make(z)
end

local closure = outer(3)
print("regress_288_luau_shared_proto_dag", closure(4))

if false then
    local function dead()
        return function()
            return 1
        end
    end
    print(dead()())
end
