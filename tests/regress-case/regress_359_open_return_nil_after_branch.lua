-- regress_359_open_return_nil_after_branch: 已结束的 root branch 不应阻止终态 nil pack 收回
-- unluac: expect-contains [[return nil, nil, ]]
-- unluac: expect-not-contains [[ = nil, nil]]

local function tail()
    return "tail"
end

local function run(flag)
    if flag then
        flag = false
    end
    return nil, nil, tail()
end

local first, second, third = run(true)
assert(first == nil and second == nil and third == "tail")
