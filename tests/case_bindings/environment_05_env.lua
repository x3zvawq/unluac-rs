-- lua52_01_env#1: _ENV环境重定向
local function test_env_redirect()
    local _ENV = {
        print = print,
        prefix = "env",
        value = 7,
    }

    print("lua52_01_env#1", prefix, value + 5)

end

-- lua52_01_env#2: _ENV遮蔽与闭包
local function test_env_shadow()
    local _ENV = {
        print = print,
        prefix = "outer",
        outer_value = 11,
    }

    local function make_reader(seed)
        local prefix = seed .. ":" .. outer_value
        local _ENV = {
            print = print,
            prefix = "inner",
            value = 7,
        }

        return function(suffix)
            local label = prefix .. "-" .. suffix
            return label, prefix, value
        end
    end

    local reader = make_reader("seed")
    print("lua52_01_env#2", prefix, outer_value, reader("tail"))
end

test_env_redirect()
test_env_shadow()
