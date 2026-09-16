-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=0]]
-- An initializer may contain nil holes and be captured after its SETLIST.
VALUES = { first = 7, third = 9 }
local t = { VALUES.first, VALUES.missing, VALUES.third }
local function read(i) return t[i] end
assert(read(1) == 7 and read(2) == nil and read(3) == 9)
assert(#t == 3)
print("captured-nil-batch", read(1), read(2), read(3), #t)
