local function read_value()
    return value
end

local env = {
    value = "from-env",
}

setfenv(read_value, env)
print("setfenv", read_value())
