-- 构造器写入共享 cell 后重新读取并返回，不需要额外的 local 往返交接。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=3]] [[@debug=retained]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=0]]
-- unluac: expect-not-contains [[= assert]]
local cell = {}

local function replace_empty()
    cell = {}
    return cell
end

local function replace_record()
    cell = {answer = 42, ready = true}
    return cell
end

local function retain_snapshot()
    local saved = cell
    cell = {}
    return saved
end

local initial = cell
local empty = replace_empty()
assert(empty == cell and empty ~= initial and next(empty) == nil)
local record = replace_record()
assert(record == cell and record ~= empty and record.answer == 42 and record.ready)
assert(retain_snapshot() == record and cell ~= record and next(cell) == nil)
print("upvalue-constructor-return", "OK")
