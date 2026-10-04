-- unluac: expect-count [[= nil, nil, nil]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=2]] [[@dialect=luajit]]
-- 原连续 nil 声明必须承接各个同槽条件写回；谓词 CALL 执行时 b 已在原槽。
-- Lua 5.5 的数值 for 少一个控制槽，故对应的 debug 索引比其它方言小一。
local saved_floor = math.floor
local function run()
    for i = 0, 1 do
        local a, b, c
        if i % 2 == 1 then a = false end
        if math.floor(i / 2) % 2 == 1 then b = 2 end
        if i >= 4 then c = true end
        assert(b == "written")
        print("values", i, a, b, c)
    end
end
math.floor = function(value)
    assert(debug.setlocal(2, _VERSION == "Lua 5.5" and 5 or 6, "written") ~= nil)
    return 0
end
local ok, err = pcall(run)
math.floor = saved_floor
assert(ok, err)
print("nil group branch prefix")
