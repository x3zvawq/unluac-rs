-- A one-use `<close>` tail is a declaration-merge candidate, not an inline-exprs candidate.
-- The literal-only substring keeps this shape contract independent of generated binding names.
-- unluac: expect-contains [[<close> = 37, nil]]

local function close_tail()
    local repeated = 37
    local resource <close> = nil
    return repeated, repeated, resource
end

local close_first, close_second, resource = close_tail()
assert(close_first == 37 and close_second == 37 and resource == nil)
print("regress_437_statement_merge_attr_handoff", close_first)
