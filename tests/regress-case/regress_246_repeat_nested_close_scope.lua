-- regress_246_repeat_nested_close_scope: 内层资源必须在 until 条件前关闭
-- unluac: expect-contains [[do]]
-- unluac: expect-contains [[<close>]]

local closes = 0
local checks = 0

local function make_closer()
    return setmetatable({}, {
        __close = function()
            closes = closes + 1
        end,
    })
end

local function done()
    checks = checks + 1
    assert(closes == checks)
    return checks == 2
end

repeat
    do
        local resource <close> = make_closer()
    end
until done()

assert(closes == 2)
print("regress_246_repeat_nested_close_scope")
