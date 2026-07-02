-- unluac: expect-contains [["\nalpha"]]
local function run()
    local value = "\nalpha"
    return #value, string.byte(value, 1), string.sub(value, 2)
end

print("regress_55_leading_newline_string", run())
