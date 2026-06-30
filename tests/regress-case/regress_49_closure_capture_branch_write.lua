-- regress_49_closure_capture_branch_write#1: closure 捕获后的分支写入必须保留为同一父级 local
-- unluac: expect-contains [[local r1_0]]
-- unluac: expect-contains [[return r1_0]]
-- unluac: expect-contains [[if p1_0 then]]
-- unluac: expect-contains [[r1_0 = 1]]
-- unluac: expect-contains [[r1_0 = 2]]

local function capture_after_seed(flag)
    local value
    local reader = function()
        return value
    end
    if flag then
        value = 1
    else
        value = 2
    end
    return reader()
end

print("regress_49_closure_capture_branch_write#1", capture_after_seed(true))
