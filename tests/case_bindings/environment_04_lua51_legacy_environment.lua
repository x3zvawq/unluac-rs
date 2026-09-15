-- lua51_01#1: setfenv环境切换
local function test_setfenv()
    local function read_value()
        return value
    end

    local env = {
        value = "from-env",
    }

    setfenv(read_value, env)
    print("lua51_01#1", read_value())
end

-- lua51_01#2: module()模块
local function test_module()
    module("legacy_mod", package.seeall)

    function banner(name)
        return "hello:" .. name
    end

    print("lua51_01#2", banner("lua"), _NAME, type(_M) == "table")
end

-- lua51_01#3: 嵌套闭包setfenv
local function test_setfenv_nested()
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
    print("lua51_01#3", read("tail"), snapshot())
end

test_setfenv()
test_module()
test_setfenv_nested()
