-- regress_401_forwarded_lvalue_eval_order: closure allocation stays before an eventful lvalue prefix

local observed
local target = setmetatable({}, {
    __index = function()
        observed = collectgarbage("count")
        return {}
    end,
})

local v01, v02, v03, v04, v05, v06, v07, v08 = 1, 2, 3, 4, 5, 6, 7, 8
local v09, v10, v11, v12, v13, v14, v15, v16 = 9, 10, 11, 12, 13, 14, 15, 16
local v17, v18, v19, v20, v21, v22, v23, v24 = 17, 18, 19, 20, 21, 22, 23, 24
local v25, v26, v27, v28, v29, v30, v31, v32 = 25, 26, 27, 28, 29, 30, 31, 32

collectgarbage("collect")
collectgarbage("stop")
local before = collectgarbage("count")
local forwarded = function()
    return v01, v02, v03, v04, v05, v06, v07, v08,
        v09, v10, v11, v12, v13, v14, v15, v16,
        v17, v18, v19, v20, v21, v22, v23, v24,
        v25, v26, v27, v28, v29, v30, v31, v32
end
target.branch.leaf = forwarded
local delta = observed - before
collectgarbage("restart")

assert(delta > 0.2, delta)
print("regress_401_forwarded_lvalue_eval_order", delta > 0.2)
