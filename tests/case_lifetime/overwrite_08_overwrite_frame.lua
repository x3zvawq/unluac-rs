-- 原 CLOSURE 重用已经出作用域的全局读取槽；闭包执行时该旧值必须已释放。
-- unluac: expect-ast-count [[local-binding]] [[6]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[do-block]] [[1]]
local weak = setmetatable({}, {__mode = "v"})
local reads = 0
local old = getmetatable(_G)
setmetatable(_G, {__index = function(_, key)
    if key == "closure_frame_observe" then
        reads = reads + 1
        weak[1] = {}
        return weak[1]
    end
end})
local function probe()
    do
        local observed = closure_frame_observe
    end
    local function invoke()
        collectgarbage("collect")
        print("closure-observed", weak[1] ~= nil)
        assert(weak[1] == nil, "old scope value survived CLOSURE overwrite")
    end
    invoke()
end
probe()
setmetatable(_G, old)
assert(reads == 1, "global lookup was skipped or repeated")
