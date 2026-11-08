-- --table-align-eq=false turns `=` alignment off: record keys of non-single-line
-- aligned tables keep single spaces around `=` even when the keys differ in width.
-- unluac: expect-contains [[    id = "op",]]
-- unluac: expect-contains [[    kind = "select",]]
-- unluac: expect-contains [[    timeout_ms = 1500,]]
-- unluac: expect-not-contains [[    id          = "op",]]
-- unluac: expect-not-contains [[    label      = "worker",]]
local options = {id = "op", kind = "select", retries = 4, timeout_ms = 1500, label = "worker", retries_budget = 9, fallback_mode = true}
print(options.id, options.timeout_ms)
