-- regress_41_negated_relational_metamethod#1: negated relational comparison must preserve NaN semantics
-- unluac: expect-contains [[not (]]
-- unluac: expect-contains [[ < ]]
-- unluac: expect-not-contains [[ <= ]]
-- unluac: expect-not-contains [[unluac error]]

local nan = 0 / 0
if nan < 1 then
else
    print("not-lt")
end
