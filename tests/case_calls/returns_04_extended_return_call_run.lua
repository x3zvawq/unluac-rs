-- regress_353_extended_return_producers: each producer keeps its complete non-tail dynamic-callee preparation run
-- unluac: expect-count [[local r4_0 =]] [[1]]
-- unluac: expect-count [[local r4_1 =]] [[1]]
-- unluac: expect-count [[local r7_0 =]] [[1]]
-- unluac: expect-count [[local r7_1 =]] [[1]]
-- unluac: expect-count [[local r11_0 =]] [[1]]
-- unluac: expect-count [[local r11_1 =]] [[1]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=4]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=7]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=11]]

do
    -- Call producer.
    local function make_value(value)
        return value
    end

    local function make_outer()
        return function(value)
            return value
        end
    end

    local function safe(value)
        local first = make_value(value)
        local outer = make_outer()
        return first, outer(value)
    end

    local first, value = safe(41)
    assert(first == 41 and value == 41)
end

do
    -- Field producer.
    local holder = { nested = { value = 47 } }

    local function make_outer()
        return function(value)
            return value
        end
    end

    local function safe(value)
        local first = holder.nested.value
        local outer = make_outer()
        return first, outer(value)
    end

    local first, value = safe(48)
    assert(first == 47 and value == 48)
end

do
    -- Method producer.
    local provider = {}

    function provider:get(value)
        return value
    end

    local function make_outer()
        return function(value)
            return value
        end
    end

    local function safe(value)
        local first = provider:get(value)
        local outer = make_outer()
        return first, outer(value)
    end

    local first, value = safe(46)
    assert(first == 46 and value == 46)
end
