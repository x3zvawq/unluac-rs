-- A previous value in a generic-for result home stops being a VM root before every iterator
-- dispatch, including the zero-iteration exit dispatch.
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[12]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[do-block]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[7]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[assign]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-binding]] [[7]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-max [[assign]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-max-count [[local ]] [[6]]

local weak = setmetatable({}, { __mode = "v" })
local released_during_dispatch = false
local dispatches = 0

local function iterator()
    collectgarbage("collect")
    collectgarbage("collect")
    released_during_dispatch = weak[1] == nil
    dispatches = dispatches + 1
    return nil
end

local function run()
    do
        local pad1, pad2, pad3, pad4, old = nil, nil, nil, nil, {}
        weak[1] = old
    end
    for ignored, item in iterator do
        error(ignored or item)
    end
    return released_during_dispatch
end

assert(run(), "old result-home root survived the zero-iteration dispatch")
assert(dispatches == 1)
print("regress_456_generic_for_exit_result_home", "OK")
