-- 函数根块和显式内层块共享尾部 RETURN 时，debug 区间与捕获关闭仍须分别恢复。
-- LuaJIT 的子 proto 编号逆序，分别定位同一个函数，避免把 hook 内层块计入。
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-count [[debug.getinfo(]] [[1]]
-- unluac: expect-contains [[observations[#observations + 1] = table.concat(names, ",")]]
-- unluac: expect-ast-count [[do-block]] [[1]]
local saved
local observations = {}

local function implicit_tail()
    local first = {}
    local second = 7
    local function keep()
        return first, second
    end
    saved = keep
end

local function explicit_tail()
    do
        local inner = {}
        local count = 9
        local function keep_inner()
            return inner, count
        end
        saved = keep_inner
    end
end

local function hook(event)
    if event == "return" then
        local fn = debug.getinfo(2, "f").func
        if fn == implicit_tail or fn == explicit_tail then
            local names = {}
            for index = 1, 32 do
                local name = debug.getlocal(2, index)
                if name == "first" or name == "second" or name == "keep"
                    or name == "inner" or name == "count" or name == "keep_inner" then
                    names[#names + 1] = name
                end
            end
            observations[#observations + 1] = table.concat(names, ",")
        end
    end
end

debug.sethook(hook, "r")
implicit_tail()
local first_value, first_count = saved()
assert(type(first_value) == "table" and first_count == 7)
explicit_tail()
local second_value, second_count = saved()
assert(type(second_value) == "table" and second_count == 9)
assert(first_value ~= second_value)
debug.sethook()
assert(#observations == 2)
print("debug_06_function_tail_scope", table.concat(observations, "|"))
