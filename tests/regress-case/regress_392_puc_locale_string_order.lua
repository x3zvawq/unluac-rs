-- unluac: expect-contains [["ä" < "z"]]
-- unluac: expect-contains [["ä" <= "z"]]

local previous_locale = os.setlocale(nil, "collate")
local locale = os.setlocale("de_DE.UTF-8", "collate")
    or os.setlocale("de_DE.utf8", "collate")
    or os.setlocale("de_DE", "collate")

local less = "ä" < "z"
local less_equal = "ä" <= "z"

if previous_locale then
    os.setlocale(previous_locale, "collate")
end

if locale then
    assert(less and less_equal)
end

print("regress_392_puc_locale_string_order", locale ~= nil, less, less_equal)
