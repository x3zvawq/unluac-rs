local function build_reader()
    local prefix = "outer"

    local function read(suffix)
        return suffix .. ":" .. prefix .. ":" .. token
    end

    setfenv(read, {
        token = "env-token",
    })

    return read, function()
        return prefix
    end
end

local read, snapshot = build_reader()
print("setfenv-nested", read("tail"), snapshot())
