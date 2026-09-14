-- unluac: expect-contains [["\194\133"]]
local function run()
    local value = "\194\133"
    return string.byte(value, 1), string.byte(value, 2), #value
end

print("regress_57_utf8_control_string", run())
