-- Several field targets share one constructor call; both field syntaxes matter.
-- unluac: expect-ast-min [[numeric-for]] [[1]]
function __reg555_collect(...)
    local total = 0
    for i = 1, select("#", ...) do
        total = total + select(i, ...).read()
    end
    return total
end

local function run()
    local callee = __reg555_collect
    local a = {}
    local b = {}
    local c = {}
    local d = {}
    local e = {}
    local f = {}
    local g = {}
    local h = {}
    a.read = function() return 1 end
    function b.read() return 2 end
    c.read = function() return 3 end
    function d.read() return 4 end
    e.read = function() return 5 end
    function f.read() return 6 end
    g.read = function() return 7 end
    function h.read() return 8 end
    return callee(a, b, c, d, e, f, g, h)
end

local function captured()
    local callee = __reg555_collect
    local a = {}
    local b = {}
    a.read = function() return a == b and 1 or 2 end
    function b.read() return b == a and 3 or 4 end
    return callee(a, b)
end

assert(run() == 36)
assert(captured() == 6)
print("regress_555_constructor_field_targets", run(), captured())
