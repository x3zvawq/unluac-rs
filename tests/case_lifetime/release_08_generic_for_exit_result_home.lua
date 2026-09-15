-- A previous value in a generic-for result home stops being a VM root before every iterator
-- dispatch, including the zero-iteration exit dispatch.
-- unluac: expect-ast-count [[generic-for]] [[1]]

local weak = setmetatable({}, { __mode = "v" })
local released_during_dispatch = false

local function iterator()
    collectgarbage("collect")
    collectgarbage("collect")
    released_during_dispatch = weak[1] == nil
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
print("regress_456_generic_for_exit_result_home", "OK")
