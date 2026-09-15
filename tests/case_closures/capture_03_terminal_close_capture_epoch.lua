-- 终结分支的 close 不能切断后续写回；分别保留 sibling writer 与 child 只读的形状。
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[local-function]] [[2]] [[@proto=0]]

local function build_sibling_writer(skip_write)
    local value
    local read = function()
        return value
    end

    if skip_write then
        return read
    end

    value = 1
    local write = function()
        value = 2
    end
    return read, write
end

local function build_parent_writer(skip_write)
    local value
    local read = function()
        return value
    end

    if skip_write then
        return read
    end

    value = 1
    return read
end

-- 两次构造之间必须拥有独立 cell；终结分支返回的 reader 始终看到 nil。
local sibling_skipped = build_sibling_writer(true)
assert(sibling_skipped() == nil)
local sibling_read, sibling_write = build_sibling_writer(false)
assert(sibling_read() == 1)
sibling_write()
assert(sibling_read() == 2)
assert(sibling_skipped() == nil)
print("regress_217_terminal_close_capture_epoch#1", "OK")

local parent_skipped = build_parent_writer(true)
assert(parent_skipped() == nil)
local parent_read = build_parent_writer(false)
assert(parent_read() == 1)
assert(parent_skipped() == nil)
print("regress_218_parent_write_terminal_capture#1", "OK")
