-- regress_363_nested_close_common_copy: a common copy may move after a nested close scope that already ended
-- unluac: expect-order [[label = "else"]] [[= "assigned"]]

local close_log = {}
local close_meta = {
    __close = function(value)
        close_log[#close_log + 1] = value.label
    end,
}

local function run(flag)
    local assigned = "assigned"
    local result
    if flag then
        do
            local resource <close> = setmetatable({ label = "then" }, close_meta)
        end
        result = assigned
    else
        do
            local resource <close> = setmetatable({ label = "else" }, close_meta)
        end
        result = assigned
    end
    return result
end

assert(run(true) == "assigned")
assert(run(false) == "assigned")
assert(table.concat(close_log, ",") == "then,else")
