-- regress_10_loop_closure_capture_slot#1: 循环内被 closure capture 的局部槽位不能和 closure 结果槽位混成同一绑定
local function build()
    local list = {}
    local i = 1
    local k = 0
    list[0] = function(value)
        k = value
    end
    ::again::
    do
        local x
        if i > 2 then
            goto done
        end
        list[i] = function(value)
            if value then
                x = value
                return
            end
            return type(x), x, k
        end
        i = i + 1
        goto again
    end
    ::done::
    return list
end

local list = build()
local first_type, first_value, first_k = list[1]()
assert(first_type == "nil" and first_value == nil and first_k == 0)
list[1](10)
list[2](20)
list[0](13)
local type1, value1, k1 = list[1]()
local type2, value2, k2 = list[2]()
assert(type1 == "number" and value1 == 10 and k1 == 13)
assert(type2 == "number" and value2 == 20 and k2 == 13)