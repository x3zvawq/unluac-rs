-- unluac: expect-contains [["\255\000A"]]
local function run()
    local value = "\255\000A"
    return #value, string.byte(value, 1), string.byte(value, 2), string.byte(value, 3)
end

print("regress_58_binary_string_bytes", run())
