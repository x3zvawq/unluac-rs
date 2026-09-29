-- regress_355_mechanical_run_root_lifetime: recovered lookup locals remain roots through the lexical block
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[7]]
local calls = 0

local function check(lhs, rhs)
    local weak_values = setmetatable({}, { __mode = "v" })
    local owner = {}
    weak_values.key = owner
    collectgarbage("stop")
    owner = nil

    local function consume(value, marker)
        assert(type(value) == "table" and marker == 42)
        calls = calls + 1
    end

    local key = weak_values.key
    local marker = lhs + rhs
    consume(key, marker)

    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    return weak_values.key ~= nil
end

assert(check(20, 22))
assert(calls == 1)
