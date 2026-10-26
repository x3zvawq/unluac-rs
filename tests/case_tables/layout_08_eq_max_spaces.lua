-- --table-align-eq-max-spaces caps the total number of spaces between a key
-- and `=` (padding plus the mandatory separator). With a cap of 2, `id`/`tag`
-- and `retries_budget`/`fallback_mode` still align (exactly two visible
-- spaces), while any wider gap starts a new alignment run instead of
-- stretching the rows past the cap.
-- unluac: expect-contains [[    id  = "op",]]
-- unluac: expect-contains [[    tag = "v1",]]
-- unluac: expect-contains [[    kind = "select",]]
-- unluac: expect-contains [[    timeout_ms = 1500,]]
-- unluac: expect-contains [[    fallback_mode  = true,]]
-- unluac: expect-not-contains [[    id   = "op",]]
-- unluac: expect-not-contains [[    id         = "op",]]
-- unluac: expect-not-contains [[    retries    = 4,]]
local options = {id = "op", tag = "v1", kind = "select", timeout_ms = 1500, retries = 4, label = "worker", retries_budget = 9, fallback_mode = true}
print(options.id, options.timeout_ms)
