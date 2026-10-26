-- --table-align-eq (default true) aligns record keys of non-single-line aligned
-- tables by `=`: every key is padded to the widest key of its alignment run, so
-- values start at the same column. Keys whose widths stay within the default
-- `--table-align-eq-max-spaces` cap (8 visible spaces) share one run.
-- unluac: expect-contains [[    id       = "op",]]
-- unluac: expect-contains [[    tag      = "v1",]]
-- unluac: expect-contains [[    kind     = "select",]]
-- unluac: expect-contains [[    attempts = 12,]]
-- unluac: expect-not-contains [[    id = "op",]]
-- unluac: expect-not-contains [[    retries = 4,]]
local options = {id = "op", tag = "v1", kind = "select", mode = "auto", state = "idle", attempt = 3, retries = 4, attempts = 12}
print(options.id, options.attempts)
