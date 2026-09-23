-- 捕获声明跨过内部条件后在独立 CLOSE 处离域，不能延长到后继调用。
-- unluac: expect-contains [[assert(reader() == (flag and "after" or "before"))]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=retained]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@debug=stripped]] [[@dialect=luajit]]
-- Luau 把只读 cell 编译为 ByValue capture，不发 CLOSE；移除 debug 后没有独立块边界证据。
-- unluac: expect-ast-count [[do-block]] [[0]] [[@debug=stripped]] [[@dialect=luau]]
local reader
local function inspect()
    if debug and debug.getlocal then
        for index = 1, 20 do
            local name = debug.getlocal(2, index)
            if not name then break end
            assert(name ~= "scoped_cell", "captured local escaped its scope")
        end
    end
end
local function run(flag)
    do
        local scoped_cell = {value = "before"}
        reader = function() return scoped_cell.value end
        if flag then
            scoped_cell.value = "after"
        end
        assert(reader() == (flag and "after" or "before"))
    end
    inspect()
end
run(true)
assert(reader() == "after")
run(false)
assert(reader() == "before")
print("scope_10_captured_branch_close", "OK")
