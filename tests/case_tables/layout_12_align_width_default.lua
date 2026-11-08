-- --table-align-width follows --max-line-length when the width option itself is
-- not set: with the global line budget lowered to 40, the aligned grid packs
-- two-digit numbers 8 per row (stride = widest cell + 2 = 4; row budget
-- 40 - 4 indent = 36 -> 9 cells max, evened out to 8 across 3 rows).
-- unluac: expect-contains [[1,  2,  3,  4,  5,  6,  7,  8,]]
-- unluac: expect-contains [[9, 10, 11, 12, 13, 14, 15, 16,]]
-- unluac: expect-contains [[17, 18, 19, 20, 21, 22, 23, 24,]]
local grid = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
print(grid[1], grid[24])
