-- 内层资源的 __close 执行时，外层 copy 的命名作用域仍有效，且 debug 写入不能留下隐藏根。
local function run(owner, gc, closer)
    local iteration = 0
    while true do
        collectgarbage("collect")
        if iteration == 1 then break end
        local current = owner
        local copy = current
        owner = nil
        do
            local guard <close> = closer
            current = gc
            current("collect")
            iteration = iteration + 1
        end
    end
end
local gc = collectgarbage
local weak = setmetatable({}, {__mode="v"})
local closer = setmetatable({}, {__close=function()
    local found = false
    for i=1,40 do
        local name=debug.getlocal(2,i)
        if not name then break end
        if name=="copy" then
            debug.setlocal(2,i,nil)
            found=true
            break
        end
    end
    if not found then error("copy missing during close") end
    gc("collect")
    if weak[1]~=nil then error("hidden copy survived close write") end
end})
local function make()
    local obj={}
    weak[1]=obj
    return obj
end
run(make(),gc,closer)
print("regress_541_nested_close_source_scope", "OK")
