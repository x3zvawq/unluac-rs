-- 转交给全局的闭包仍有独立局部根，后续闭包不能提前覆盖它的原槽。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=0]]
collectgarbage("stop")
local weak = setmetatable({}, {__mode = "v"})
local forwarded = function() return 4 end
forwarded_global_root_target = forwarded
weak[1] = forwarded_global_root_target
local function clear()
    forwarded_global_root_target = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] ~= nil, "forwarded closure lost its source root")
    assert(weak[1]() == 4)
end
clear()
collectgarbage("restart")
print("forwarded-global-root")
