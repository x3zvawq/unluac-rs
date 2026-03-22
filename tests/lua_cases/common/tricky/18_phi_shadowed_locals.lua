local function choose(flag)
    local value = "root"

    if flag then
        local value = "branch"
        if #value > 0 then
            print("shadow", value .. "-if")
        end

        value = value .. "-mut"
        return value
    end

    do
        local value = "else"
        print("shadow", value)
    end

    return value
end

print("shadow", choose(true), choose(false))
