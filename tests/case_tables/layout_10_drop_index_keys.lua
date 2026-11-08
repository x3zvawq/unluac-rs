-- --table-drop-index-keys=true rewrites contiguous explicit `[1]..[n]` constructor
-- keys as positional array entries. Bytecode keeps such keys faithfully (the original
-- source wrote them out), so this is opt-in: evaluation order and per-field side
-- effects are preserved, only the unspecified pairs() order changes.
-- Tables with gaps, descending keys or mixed positional fields stay untouched.
-- unluac: expect-contains [[= { "alpha", "beta" }]]
-- unluac: expect-contains [[{ mode = "dlg", "alpha", "beta", tag = 3 }]]
-- unluac: expect-contains [[    10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,]]
-- unluac: expect-contains [[    25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,]]
-- unluac: expect-not-contains [[[1] = "alpha", [2] = "beta"]]
-- unluac: expect-not-contains [[[1] = 10]]
-- unluac: expect-contains [[[1] = "alpha", [3] = "gamma"]]
-- unluac: expect-contains [[[2] = "beta", [1] = "alpha"]]
local keyed = {[1] = "alpha", [2] = "beta"}
local mixed = {mode = "dlg", [1] = "alpha", [2] = "beta", tag = 3}
local grid = {[1] = 10, [2] = 11, [3] = 12, [4] = 13, [5] = 14, [6] = 15, [7] = 16, [8] = 17, [9] = 18, [10] = 19, [11] = 20, [12] = 21, [13] = 22, [14] = 23, [15] = 24, [16] = 25, [17] = 26, [18] = 27, [19] = 28, [20] = 29, [21] = 30, [22] = 31, [23] = 32, [24] = 33, [25] = 34, [26] = 35, [27] = 36, [28] = 37, [29] = 38, [30] = 39}
local sparse = {[1] = "alpha", [3] = "gamma"}
local reverse = {[2] = "beta", [1] = "alpha"}
print(keyed[1], mixed.mode, grid[30], sparse[3], reverse[2])
