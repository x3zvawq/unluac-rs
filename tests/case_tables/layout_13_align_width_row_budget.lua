-- --table-align-width budgets every candidate row of an aligned table (the
-- flat one-liner, the packed content line and grid rows), not only grid rows:
-- both constructors below fit the default 100-column line budget, but their
-- flat/content forms exceed the 40-column table width, so they must stay
-- expanded one entry per line instead of collapsing into over-wide rows.
-- unluac: expect-not-contains [[aa = 1, bb = 2]]
-- unluac: expect-not-contains [[fielda = 1, fieldb = 2]]
-- unluac: expect-contains [[    aa = 1,]]
-- unluac: expect-contains [[    fielda = 1,]]
-- unluac: expect-contains [[    fieldh = 8,]]
local small = {aa = 1, bb = 2, cc = 3, dd = 4, ee = 5, ff = 6}
local large = {fielda = 1, fieldb = 2, fieldc = 3, fieldd = 4, fielde = 5, fieldf = 6, fieldg = 7, fieldh = 8}
print(small.aa, small.ff, large.fielda, large.fieldh)
