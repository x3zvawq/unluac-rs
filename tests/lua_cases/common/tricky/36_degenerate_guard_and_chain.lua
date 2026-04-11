-- Exercises `(A or B) and C` patterns where the `and C` guard compiles to a
-- degenerate TEST block (both CFG edges point to the same successor) because
-- the if-then body is empty or the guard is the last condition before merge.
-- The decompiler must fold the degenerate guard back into the short-circuit
-- condition instead of silently dropping it.

local a = 1
local b = true

-- Case 1: empty body – `and b` produces a degenerate TEST block
if (a == 1 or a == 2) and b then
end

-- Case 2: non-empty body
if (a == 1 or a == 2) and b then
    print("body")
end

-- Case 3: longer or-chain with trailing guard
if (a == 1 or a == 2 or a == 3) and b then
    print("three")
end
