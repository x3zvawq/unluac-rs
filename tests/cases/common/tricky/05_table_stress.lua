local function table_stress()
    local t = {
        [1] = "hex",
        key = {
            inner = 42,
        },
        1,
        2,
        3,
    }

    t[1] = t.key.inner + t[2] + #t

    local nested_call = string.upper(string.sub(t[1] .. "hello", 1, 5))
    return t, nested_call
end

local t, nested_call = table_stress()
print("table-stress", t[1], t[2], t[3], t.key.inner, nested_call)
