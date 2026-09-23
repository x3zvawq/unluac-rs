-- A declaration sunk into one branch must still cover writes in its sibling suffix.
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=0]]
local environment = _ENV or getfenv()
local original_keys = {}
for key in pairs(environment) do
    original_keys[key] = true
end

local function run(enabled)
    for _, value in ipairs({ 0, 3 }) do
        repeat
            value = value + 1
            if enabled then break end
            value = value + 2
        until value >= 6
        print(enabled, value)
    end
end
run(true)
run(false)

local added = 0
for key in pairs(environment) do
    if not original_keys[key] then added = added + 1 end
end
assert(added == 0, "declaration sinking introduced a global write")
print("regress_517_decl_sink_write_scope", added)
