-- regress_344_tail_do_same_exit: a function-tail close still runs once when debug scope keeps the do
-- unluac: expect-ast-min [[do-block]] [[1]] [[@proto=1]] [[@debug=retained]]
-- unluac: expect-ast-count [[close-binding]] [[1]] [[@proto=1]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[10]]
-- unluac: expect-ast-count [[do-block]] [[3]]

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

-- debug 尾块保留原 Close 终点；回边的早期 Close 不能把 tail 挤出 outer。
-- 资源预先构造，以单独观察资源作用域而不混入初始化 CALL 的寄存器帧。
-- unluac: expect-ast-count [[close-binding]] [[2]] [[@proto=5]]
local log = {}
local outer_resource = setmetatable({}, {
    __close = function() log[#log + 1] = "outer" end,
})
local inner_resource = setmetatable({}, {
    __close = function() log[#log + 1] = "inner" end,
})
local n = 0
local function run_tail()
    ::again::
    do
        local outer <close> = outer_resource
        do
            local inner <close> = inner_resource
            if n == 0 then n = 1; goto again end
        end
        log[#log + 1] = "tail"
    end
end
run_tail()
assert(table.concat(log, ",") == "inner,outer,inner,tail,outer", table.concat(log, ","))
