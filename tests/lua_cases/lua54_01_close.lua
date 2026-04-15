-- lua54_01_close#1: to-be-closed基础
local function test_tbc_basic()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    do
        local resource <close> = make_resource("res")
        log[#log + 1] = "body:" .. resource.name
    end

    print("lua54_01_close#1", table.concat(log, "|"))
end

-- lua54_01_close#2: to-be-closed多出口
local function test_tbc_multi_exit()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function consume(mode)
        local out = {}

        do
            local first <close> = make_resource("first:" .. mode)
            out[#out + 1] = first.name

            while true do
                local second <close> = make_resource("second:" .. mode)
                out[#out + 1] = second.name

                if mode == "return" then
                    return out
                end

                if mode == "break" then
                    break
                end

                out[#out + 1] = first.name .. "+" .. second.name
                break
            end

            out[#out + 1] = "after:" .. first.name
        end

        return out
    end

    print("lua54_01_close#2", table.concat(consume("break"), ","))

    print("lua54_01_close#2", table.concat(consume("return"), ","))

    print("lua54_01_close#2", table.concat(log, "|"))

end

-- lua54_01_close#3: goto重入与close
local function test_tbc_goto_reenter()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local turn = 1

    do
        local outer <close> = make_resource("outer")

        ::again::
        do
            local inner <close> = make_resource("inner:" .. turn)
            if turn < 3 then
                turn = turn + 1
                goto again
            end

            log[#log + 1] = outer.name .. "+" .. inner.name
        end
    end

    print("lua54_01_close#3", table.concat(log, "|"))

end

-- lua54_01_close#4: close与尾调用屏障
local function test_close_tailcall()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function invoke(fn, ...)
        return fn(...)
    end

    local function finalize(tag, mode, ...)
        local resource <close> = make_resource(tag)

        local function build(...)
            local parts = { ... }
            parts[#parts + 1] = resource.name
            return table.concat(parts, ":")
        end

        if mode == "tail" then
            return invoke(build, ...)
        end

        return build(...)
    end

    print("lua54_01_close#4", finalize("alpha", "tail", "x", "y"))

    print("lua54_01_close#4", finalize("beta", "plain", "m"))

    print("lua54_01_close#4", table.concat(log, "|"))

end

-- lua54_01_close#5: 泛型for与const close
local function test_for_const_close()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function list_iter(values)
        local index = 0
        return function()
            index = index + 1
            if index <= #values then
                return index, values[index], #values - index
            end
        end
    end

    local out = {}

    for index, value, remaining in list_iter({ "aa", "bbb", "c" }) do
        local prefix <const> = value .. ":" .. index
        do
            local resource <close> = make_resource(prefix)
            if remaining % 2 == 0 then
                out[#out + 1] = resource.name .. ":even"
            else
                out[#out + 1] = resource.name .. ":odd"
            end
        end
    end

    print("lua54_01_close#5", table.concat(out, "|"))

    print("lua54_01_close#5", table.concat(log, "|"))

end

test_tbc_basic()
test_tbc_multi_exit()
test_tbc_goto_reenter()
test_close_tailcall()
test_for_const_close()
