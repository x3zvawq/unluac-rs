local function ultimate_mess(root, a, b, c)
    local x = ((a and b) or c) and (b or (c and a)) or (not a and not b)
    local branch = root.branches[a and "t" or "f"]
    local item = branch.items[(b and 1 or 2)]

    return x and "T" or "F", item.value
end

local input = {
    branches = {
        t = {
            items = {
                { value = 11 },
                { value = 22 },
            },
        },
        f = {
            items = {
                { value = 33 },
                { value = 44 },
            },
        },
    },
}

print("mess", ultimate_mess(input, true, false, true))
print("mess", ultimate_mess(input, true, true, false))
print("mess", ultimate_mess(input, false, false, true))
