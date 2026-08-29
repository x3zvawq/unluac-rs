-- unluac: expect-not-contains [[ == nil]]

local function discard_literal_equality(value)
    local unused = value == nil
    if 1 == 1 then
        print("discard-literal-equality", value)
    else
        print("unreachable", unused)
    end
end

discard_literal_equality(false)
