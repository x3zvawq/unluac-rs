-- regress_344_tail_do_same_exit: a function-tail close still runs once when debug scope keeps the do
-- unluac: expect-ast-min [[do-block]] [[1]] [[@proto=1]] [[@debug=retained]]
-- unluac: expect-ast-count [[close-binding]] [[1]] [[@proto=1]] [[@debug=retained]]

local closed = 0

local function run()
    do
        local resource <close> = setmetatable({}, {
            __close = function()
                closed = closed + 1
            end,
        })
        assert(resource)
        return "ok"
    end
end

assert(run() == "ok")
assert(closed == 1)
