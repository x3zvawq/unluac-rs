-- regress_353_extended_return_producer_order: call and field producers stay ahead of the return-prefix event

do
    -- Call producer: v -> o -> p.
    local trace = ""

    local function make_value(value)
        trace = trace .. "v"
        return value
    end

    local function make_outer()
        trace = trace .. "o"
        return function(value)
            return value
        end
    end

    local function observe()
        trace = trace .. "p"
        return trace
    end

    local function unsafe(value)
        trace = ""
        local first = make_value(value)
        local outer = make_outer()
        return observe(), first, outer(value)
    end

    local prefix, first, value = unsafe(42)
    assert(prefix == "vop" and first == 42 and value == 42 and trace == "vop")
end

do
    -- Field producer: l -> o -> p.
    local trace = ""

    local source = setmetatable({}, {
        __index = function()
            trace = trace .. "l"
            return 49
        end,
    })

    local function make_outer()
        trace = trace .. "o"
        return function(value)
            return value
        end
    end

    local function observe()
        trace = trace .. "p"
        return trace
    end

    local function unsafe(value)
        trace = ""
        local first = source.value
        local outer = make_outer()
        return observe(), first, outer(value)
    end

    local prefix, first, value = unsafe(50)
    assert(prefix == "lop" and first == 49 and value == 50 and trace == "lop")
end
