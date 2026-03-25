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
print("env-shadow", prefix, outer_value, reader("tail"))
