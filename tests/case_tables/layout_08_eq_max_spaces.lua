-- --table-align-eq-max-spaces caps the padding of `=` alignment: with a cap of 2
-- the 10-char timeout_ms key would need 8 padding spaces after `id`, so the run
-- breaks and the remaining keys keep single spaces instead of stretching rows.
-- unluac: expect-contains [[    id   = "op",]]
-- unluac: expect-contains [[    kind = "select",]]
-- unluac: expect-contains [[    retries = 4,]]
-- unluac: expect-contains [[    timeout_ms = 1500,]]
-- unluac: expect-not-contains [[    id         = "op",]]
-- unluac: expect-not-contains [[    kind       = "select",]]
local options = {id = "op", kind = "select", retries = 4, timeout_ms = 1500, label = "worker", retries_budget = 9, fallback_mode = true}
print(options.id, options.timeout_ms)
