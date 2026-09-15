-- Copies share an allocation site; every physical home keeps its own release endpoint.
-- unluac: expect-ast-min [[local-decl]] [[32]]
local weak = setmetatable({}, { __mode = "v" })
local function run()
    local first = {}
    local second = {}
    weak[1], weak[2] = first, second
    local a0 = first
    local a1 = first
    local a2 = first
    local a3 = first
    local a4 = first
    local a5 = first
    local a6 = first
    local a7 = first
    local a8 = first
    local a9 = first
    local a10 = first
    local a11 = first
    local a12 = first
    local a13 = first
    local a14 = first
    local a15 = first
    local b0 = second
    local b1 = second
    local b2 = second
    local b3 = second
    local b4 = second
    local b5 = second
    local b6 = second
    local b7 = second
    local b8 = second
    local b9 = second
    local b10 = second
    local b11 = second
    local b12 = second
    local b13 = second
    local b14 = second
    local b15 = second
    first = nil
    second = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil and weak[2] ~= nil)
    a0 = b0
    a1 = b1
    a2 = b2
    a3 = b3
    a4 = b4
    a5 = b5
    a6 = b6
    a7 = b7
    a8 = b8
    a9 = b9
    a10 = b10
    a11 = b11
    a12 = b12
    a13 = b13
    a14 = b14
    a15 = b15
    collectgarbage("collect")
    assert(weak[1] == nil and weak[2] ~= nil)
    a0 = nil
    a1 = nil
    a2 = nil
    a3 = nil
    a4 = nil
    a5 = nil
    a6 = nil
    a7 = nil
    a8 = nil
    a9 = nil
    a10 = nil
    a11 = nil
    a12 = nil
    a13 = nil
    a14 = nil
    a15 = nil
    b0 = nil
    b1 = nil
    b2 = nil
    b3 = nil
    b4 = nil
    b5 = nil
    b6 = nil
    b7 = nil
    b8 = nil
    b9 = nil
    b10 = nil
    b11 = nil
    b12 = nil
    b13 = nil
    b14 = nil
    b15 = nil
    collectgarbage("collect")
    assert(weak[2] == nil)
end
run()
print("allocation-home-index", "OK")
