-- regress_588: 原数组缓冲与低槽读取组成初始化，保留 NaN 捕获和接收调用的参数语境。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function captured_nan()
    local value = ({ 0 / 0 })[1]
    local function factory()
        return function()
            return value
        end
    end
    local first = factory()
    local second = factory()
    assert(first ~= second)
    assert(first() ~= first() and second() ~= second())
    print("array-capture", first == second, first() ~= first())
end

local function retained_box()
    local box = { 0 / 0 }
    local value = box[1]
    local function capture()
        return value
    end
    box[1] = 7
    assert(box[1] == 7 and capture() ~= capture())
    print("array-alias", box[1], capture() ~= capture())
end

local function argument_snapshot()
    local trace = {}
    local callee
    local original = setmetatable({}, {
        __call = function(_, first, second)
            trace[#trace + 1] = "old"
            return first .. second
        end,
    })
    callee = original
    local function replacement()
        trace[#trace + 1] = "new"
        return "wrong"
    end
    local function argument()
        trace[#trace + 1] = "argument"
        callee = replacement
        return "right"
    end
    local result = callee(({ "left" })[1], argument())
    assert(result == "leftright" and table.concat(trace, ",") == "argument,old")
    assert(callee == replacement)
    print("array-argument", result, table.concat(trace, ","))
end

local function nil_slot()
    local value = ({ nil })[1]
    local function capture()
        return value
    end
    assert(capture() == nil)
    print("array-nil", capture() == nil)
end

captured_nan()
retained_box()
argument_snapshot()
nil_slot()
