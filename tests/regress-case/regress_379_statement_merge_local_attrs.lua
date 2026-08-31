-- Attribute-bearing locals may share one declaration when their RHS suffix is eventless.
-- unluac: expect-contains [[copy, owned <close>]]
-- unluac: expect-not-contains [[early <close>, late]]
-- unluac: expect-not-contains [[first <close>, second <close>]]

local close_log = {}
local close_meta = {
    __close = function(self)
        close_log[#close_log + 1] = self.label
    end,
}

local function merge_one_close(resource, value)
    local copy = value
    local owned <close> = resource
    assert(owned == resource and copy == value)
    return owned.label, copy, copy
end

local resource = setmetatable({ label = "owned" }, close_meta)
local label, first_copy, second_copy = merge_one_close(resource, 37)
assert(label == "owned" and first_copy == 37 and second_copy == 37)
assert(close_log[1] == "owned")

local function keep_close_trailing(resource, value)
    local early <close> = resource
    local late = value
    assert(early == resource and late == value)
    return early.label, late, late
end

local early_resource = setmetatable({ label = "early" }, close_meta)
local early_label, first_late, second_late = keep_close_trailing(early_resource, 41)
assert(early_label == "early" and first_late == 41 and second_late == 41)
assert(close_log[2] == "early")

local function keep_two_closes(first_resource, second_resource)
    local first <close> = first_resource
    local second <close> = second_resource
    assert(first == first_resource and second == second_resource)
    return first.label, second.label
end

local first_resource = setmetatable({ label = "first" }, close_meta)
local second_resource = setmetatable({ label = "second" }, close_meta)
local first_label, second_label = keep_two_closes(first_resource, second_resource)
assert(first_label == "first" and second_label == "second")
assert(close_log[3] == "second" and close_log[4] == "first")

print(
    "regress379",
    label,
    first_copy,
    second_copy,
    early_label,
    first_late,
    second_late,
    first_label,
    second_label
)
