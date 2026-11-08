-- --table-align-cells=right forces every grid kind right: the padding moves
-- before each cell so trailing commas land on one shared column (the layout
-- strings had before the per-kind auto default existed).
-- unluac: expect-contains [[      "peninsula", "archipelago",   "mountains",   "waterfall",  "wilderness", "undergrowth",]]
-- unluac: expect-contains [[      "tableland",   "watershed",    "lowlands",   "foothills",       "basin",]]
-- unluac: expect-not-contains [[    "peninsula",   "archipelago",]]
local labels = {"peninsula", "archipelago", "mountains", "waterfall", "wilderness", "undergrowth", "tableland", "watershed", "lowlands", "foothills", "basin"}
print(labels[1], labels[#labels])
