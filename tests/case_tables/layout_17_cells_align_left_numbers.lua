-- --table-align-cells=left forces number grids left: mixed one- and two-digit
-- values stop being right-aligned within their column and start on a shared
-- left edge instead; the per-row cell count stays governed by
-- --table-align-width (follows --max-line-length by default).
-- unluac: expect-contains [[    3,  40, 77, 25, 62, 10, 47, 84, 32, 69, 17, 54, 91, 39, 76, 24, 61, 9,  46, 83,]]
-- unluac: expect-contains [[    31, 68, 16, 53, 90, 38, 75, 23, 60, 8,  45, 82, 30, 67, 15, 52, 89, 37, 74, 22,]]
-- unluac: expect-not-contains [[    91, 39, 76,]]
local values = {3, 40, 77, 25, 62, 10, 47, 84, 32, 69, 17, 54, 91, 39, 76, 24, 61, 9, 46, 83, 31, 68, 16, 53, 90, 38, 75, 23, 60, 8, 45, 82, 30, 67, 15, 52, 89, 37, 74, 22}
print(values[1], values[#values])
