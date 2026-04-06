local x = 1
local function get()
    return x
end

print("number-first", get())
x = 2
print("number-second", get(), x)

local log = {}
local function mark(name)
    log[#log + 1] = name
end

mark("a")
print("table-first", table.concat(log, ","))
log = {}
mark("b")
print("table-second", table.concat(log, ","))
