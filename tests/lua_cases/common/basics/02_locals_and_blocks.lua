local name = "outer"

do
    local name = "inner"
    local value = name .. "-block"
    print("scope", name, value)
end

print("scope", name)
