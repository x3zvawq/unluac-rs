-- 首项必须在第二项清空前保存旧 closure，完整赋值不能留下独立快照与 callee 交接。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-not-contains [[ = assert]]
local function transfer(flag)
    local left, right
    local read_left = function() return left end
    local read_right = function() return right end
    read_left, read_right = read_right, read_left
    if flag then left = true else left = false end
    if flag then right = false else right = true end
    assert(read_left() == not flag)
    assert(read_right() == flag)
    read_right, read_left = read_left, nil
    if flag then right = true else right = false end
    assert(read_right() == flag)
    assert(read_left == nil)
end
transfer(true)
transfer(false)
print("copy_nil_frame", "OK")
