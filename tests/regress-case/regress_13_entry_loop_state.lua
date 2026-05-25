-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[if ]]
-- unluac: expect-contains [[< 10]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved(multi-value use]]

local function f(v)
    while v do
        if v < 10 then
            v = 20
        else
            v = nil
        end
    end
end

return f
