-- Without --table-drop-index-keys, explicit `[1]..[n]` constructor keys are kept
-- exactly as the bytecode stored them: decompiled output stays faithful to the
-- original source, including tables that the projection above would rewrite.
-- unluac: expect-contains [[[1] = "alpha", [2] = "beta"]]
-- unluac: expect-contains [[[2] = "beta", [1] = "alpha"]]
local keyed = {[1] = "alpha", [2] = "beta"}
local reverse = {[2] = "beta", [1] = "alpha"}
print(keyed[1], reverse[2])
