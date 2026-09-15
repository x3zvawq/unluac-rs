-- regress_189_terminal_empty_return_guard#1: 空 return guard 不与尾 return 清理反复互换
-- unluac: expect-contains [[pcall]]
-- unluac: expect-not-contains [[unluac error]]

local function run()
    if pcall(function()
        print("regress_189_terminal_empty_return_guard#1")
    end, nil) then
        return
    else
        return
    end
end

run()
