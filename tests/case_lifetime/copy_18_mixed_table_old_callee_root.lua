-- 旧 callee 的槽必须在首个字段求值前由 NEWTABLE 覆盖；显式 local 对照须继续持有旧根。
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=4]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=5]]
local weak

local function make_callable()
    return setmetatable({}, {
        __call = function(self)
            weak[self] = true
        end,
    })
end

local function old_callee_was_collected()
    collectgarbage("collect")
    return next(weak) == nil
end

local function direct_seed_overwrite()
    weak = setmetatable({}, { __mode = "k" })
    make_callable()()
    local rows = { { old_callee_was_collected() }, key = { value = 3 }, [{ 2 }] = 3 }
    return rows[1][1]
end

local function delayed_overwrite_control()
    weak = setmetatable({}, { __mode = "k" })
    local old_callee = make_callable()
    old_callee()
    local rows = { { old_callee_was_collected() }, key = { value = 3 }, [{ 2 }] = 3 }
    return rows[1][1]
end

local early = direct_seed_overwrite()
local delayed = delayed_overwrite_control()
print("mixed-key-old-callee-root", early, delayed)
assert(early == true)
assert(delayed == false)
