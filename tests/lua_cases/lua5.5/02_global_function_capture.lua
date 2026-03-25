global none, print
global outer_prefix, global_bias = "G", 4
global emit

local function install(tag)
    local prefix = tag .. ":" .. outer_prefix
    local hop = global_bias * #tag

    global function emit(x)
        local mixed = x * hop + #prefix
        return prefix, mixed, outer_prefix .. ":" .. global_bias
    end
end

install("ax")
global_bias = global_bias + 3
outer_prefix = outer_prefix .. "!"

local a1, b1, c1 = emit(2)
local a2, b2, c2 = emit(5)

print("g55-capture", a1, b1, c1, a2, b2, c2)
