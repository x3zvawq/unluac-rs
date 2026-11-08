-- --table-align-width shrinks the per-row cell budget of the aligned grid:
-- with a 40-column budget two-digit numbers pack 8 per row (default 100 would
-- pack 15), proving the option drives the renderer row math, not the default.
-- unluac: expect-contains [[    10, 11, 12, 13, 14, 15, 16, 17,]]
-- unluac: expect-contains [[    18, 19, 20, 21, 22, 23, 24, 25,]]
-- unluac: expect-contains [[    26, 27, 28, 29, 30, 31, 32, 33,]]
-- unluac: expect-contains [[    34, 35, 36, 37, 38, 39,]]
-- unluac: expect-not-contains [[16, 17, 18,]]
local values = {10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39}
print(values[1], values[30])
