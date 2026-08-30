-- regress_344_tail_do_same_exit: a function-tail close still runs once when debug scope keeps the do

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
