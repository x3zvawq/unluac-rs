-- regress_181_generic_for_branch_phi#1: generic-for body 的局部分支 Phi 归本轮 soft merge

local function run(text, should_break)
    local values = {}
    local last = nil
    for char in text:gmatch(".") do
        local value = nil
        if char == "A" then
            value = 1
        elseif char == "B" then
            value = 2
        elseif char == "N" and should_break then
            break
        end
        if value then
            values[#values + 1] = value
            last = value
        end
    end
    return last
end

print("regress_181_generic_for_branch_phi#1", run("BA", false))
