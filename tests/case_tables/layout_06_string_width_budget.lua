-- --table-align-string-width caps the rendered string width allowed in a grid:
-- with a cap of 6 the 13-char long labels disqualify the whole table from grid
-- mode (one entry per line instead), while 5-char short labels stay gridded,
-- proving the cap disqualifies only over-wide strings, not strings in general.
-- unluac: expect-contains [[    "longstring1",]]
-- unluac: expect-contains [[    "longstring9",]]
-- unluac: expect-not-contains [[    "longstring1", "longstring2",]]
-- unluac: expect-contains [[    "k01", "k02", "k03", "k04", "k05", "k06", "k07", "k08", "k09", "k10",]]
-- unluac: expect-contains [[    "k21", "k22", "k23", "k24", "k25", "k26", "k27", "k28", "k29", "k30",]]
local long_labels = {"longstring1", "longstring2", "longstring3", "longstring4", "longstring5", "longstring6", "longstring7", "longstring8", "longstring9"}
local short_labels = {"k01", "k02", "k03", "k04", "k05", "k06", "k07", "k08", "k09", "k10", "k11", "k12", "k13", "k14", "k15", "k16", "k17", "k18", "k19", "k20", "k21", "k22", "k23", "k24", "k25", "k26", "k27", "k28", "k29", "k30"}
print(long_labels[1], short_labels[30])
