-- 内层入口两臂都留在内层；break pad 与正常完成均先进入外层尾条件。
-- unluac: expect-ast-min [[repeat]] [[2]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@dialect=luau]]
local function run(a, b, c, d)
    repeat
        repeat
            if b then
                if c then break else print("regress_644#1", "else") end
            end
        until d
    until a
end

-- 经表调用保留待测函数的执行，避免 O2 只执行已内联的常量调用结果。
local callbacks = {run}
for mode = 0, 2 do
    print("regress_644#1", "mode", mode)
    callbacks[1](true, mode ~= 0, mode == 1, true)
end
