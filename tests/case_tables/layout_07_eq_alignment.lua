-- --table-align-eq (default true) aligns record keys of non-single-line aligned
-- tables by `=`: every key is padded to the widest key of its alignment run, so
-- values start at the same column.
-- unluac: expect-contains [[    id         = "op",]]
-- unluac: expect-contains [[    kind       = "select",]]
-- unluac: expect-contains [[    retries    = 4,]]
-- unluac: expect-contains [[    timeout_ms = 1500,]]
-- unluac: expect-contains [[    label      = "worker",]]
-- unluac: expect-not-contains [[    id = "op",]]
-- unluac: expect-not-contains [[    retries = 4,]]
local options = {id = "op", kind = "select", retries = 4, timeout_ms = 1500, label = "worker", retries_budget = 9, fallback_mode = true}
print(options.id, options.timeout_ms)
