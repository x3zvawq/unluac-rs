-- Literal truthiness exposed after alias cleanup should not retain a mechanical `not` shell.
-- unluac: expect-contains [[return false]]
-- unluac: expect-not-contains [[not 7]]

local function folded_literal_not()
    local value = 7
    return not value
end

assert(folded_literal_not() == false)
print("regress_439_literal_not_truthiness", "OK")
