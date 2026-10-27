-- aligned style keeps tables that fit inside one line flat, and applies
-- the same three-way rule to nested tables at their own indentation.
-- Assertions avoid local names: stripped chunks rename them via fallback naming.
-- unluac: expect-contains [[= { 10, 20, 30 }]]
-- unluac: expect-contains [[= { version = "1.0", flags = { true, false } }]]
-- unluac: expect-contains [[1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,]]
-- unluac: expect-contains [[    label = "board",]]
local anchors = {10, 20, 30}
local meta = {version = "1.0", flags = {true, false}}
local small = {1, 2}
local board = {
    row = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40},
    label = "board",
}
print(anchors[1], meta.version, small[2], board.row[40])
