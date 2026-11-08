-- --table-align-cells defaults to auto: string grids left-align so word-like
-- values share a common left edge (padding sits after each comma, not before
-- the next value). Numbers keep right-align; this file pins the string side.
-- unluac: expect-contains [[    "peninsula",   "archipelago", "mountains",   "waterfall",   "wilderness",  "undergrowth",]]
-- unluac: expect-contains [[    "tableland",   "watershed",   "lowlands",    "foothills",   "basin",]]
-- unluac: expect-not-contains [[      "peninsula",]]
local labels = {"peninsula", "archipelago", "mountains", "waterfall", "wilderness", "undergrowth", "tableland", "watershed", "lowlands", "foothills", "basin"}
print(labels[1], labels[#labels])
