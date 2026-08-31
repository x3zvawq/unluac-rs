-- regress_344_tail_do_same_exit: a function-tail do shares the function's exit
-- unluac: expect-not-contains [[    do]]

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
