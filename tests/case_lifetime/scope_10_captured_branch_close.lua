-- 捕获声明跨过内部条件后在独立 CLOSE 处离域，不能延长到后继调用。
-- Luau 的 ByValue capture 不发 CLOSE；后继调用覆盖原对象槽，仍证明该声明在调用前离域。
local reader
local inspections = 0
local function inspect()
    inspections = inspections + 1
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
local first_reader = reader
run(false)
assert(reader() == "before")
assert(first_reader ~= reader and first_reader() == "after" and inspections == 2)
print("scope_10_captured_branch_close", "OK")
