-- 05 的返回值在 __close 前求值；正常退出与错误展开都只关闭一次。
-- unluac: expect-contains [[<close>]]
-- unluac: expect-contains [[.name .. ":" .. tostring(]]
-- unluac: expect-not-contains [[= tostring(]]
local function make_resource(log)
    local resource <close> = setmetatable({name = "buffer"}, {
        __close = function(value, message)
            log[#log + 1] = value.name .. ":" .. tostring(message)
        end,
    })
    local size <const> = #resource.name
    if size > 0 then
        log[#log + 1] = resource.name .. ":" .. tostring(size)
    end
    return #log
end
local log = {}
local count = make_resource(log)
assert(count == 1 and #log == 2)
assert(table.concat(log, ",") == "buffer:6,buffer:nil")

local marker = {}
local close_count = 0
local function fail()
    local resource <close> = setmetatable({name = "error-buffer"}, {
        __close = function(value, message)
            assert(value.name == "error-buffer" and message == marker)
            close_count = close_count + 1
            log[#log + 1] = "closed-error"
        end,
    })
    log[#log + 1] = resource.name
    error(marker)
end
local ok, message = pcall(fail)
assert(not ok and message == marker and close_count == 1)
assert(log[3] == "error-buffer" and log[4] == "closed-error")
print("close-return-error", count, close_count, table.concat(log, ","))
