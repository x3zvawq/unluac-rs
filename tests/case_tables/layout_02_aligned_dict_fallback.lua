-- aligned style falls back to one entry per line for dictionaries and
-- for arrays whose strings exceed the aligned string width; every multi-line
-- entry keeps a trailing comma so appending a field never rewrites earlier lines.
-- Record keys are aligned by `=` (default table_align_eq), padded to the widest
-- key of their alignment run.
-- unluac: expect-contains [[    name    = "unluac",]]
-- unluac: expect-contains [[    "averylongcolorname6",]]
-- unluac: expect-contains [[    paths   = { "/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua" },]]
local config = {
    name = "unluac",
    threads = 4,
    paths = {"/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua"},
    retries = 3,
}
local palette = {"averylongcolorname1", "averylongcolorname2", "averylongcolorname3", "averylongcolorname4", "averylongcolorname5", "averylongcolorname6"}
print(config.name, config.threads, config.paths[1], palette[1])
