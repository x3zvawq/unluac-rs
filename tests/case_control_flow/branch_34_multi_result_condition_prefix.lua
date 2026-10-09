-- 条件闭包必须保留固定三返回调用；只读第三结果也不能将整次调用吞掉。
local calls = 0
local kind = 3
local distance_value = 7
function GetGrid(p) return 10 end
function Count() return 1 end
function GetData(i) return {0, 0, kind} end
function Dist(a, b) calls = calls + 1; return 0, 0, distance_value end
function Candidate(p)
    local grid = GetGrid(p) or 0
    if grid <= 0 then return false end
    for i = 1, Count() do
        local data = GetData(i)
        local kind = data and data[3] or 0
        if 1 <= kind and kind <= 6 then
            local _, _, distance = Dist(grid, i)
            if distance ~= nil then return true end
        end
    end
    return false
end
assert(Candidate(1) == true and calls == 1)
kind = 9
assert(Candidate(1) == false and calls == 1)
kind = 3
distance_value = nil
assert(Candidate(1) == false and calls == 2)
print("conditional-multi-result", calls)
