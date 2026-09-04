-- regress_477_capture_creation_reads: 直接读取、创建时快照与引用 cell 分别保留其读写时机。
local function first(value, unused)
    return value
end

local function direct_and_capture(flag)
    local value
    if flag then value = true else value = false end
    return first(value, function() return value end)
end

local function snapshot(flag)
    local value
    if flag then value = true else value = false end
    return function() return value end
end

local function reference(flag)
    local value
    if flag then value = true else value = false end
    local read = function() return value end
    value = not value
    return read()
end

for _, flag in ipairs({false, true}) do
    assert(direct_and_capture(flag) == flag)
    assert(snapshot(flag)() == flag)
    assert(reference(flag) == not flag)
end
print("regress_477_capture_creation_reads", "OK")
