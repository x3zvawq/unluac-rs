-- generic-for 体内 if/elseif 链的两臂都自然完成本轮迭代（正常路径都回到循环 header），
-- header 就是源码层 if/else 的合流边界；不得把其中一臂的回边当成非 tail backedge
-- 而要求方言不支持的 goto/label（json4lua isArray 的真实语料形状）。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-ast-min [[if]] [[3]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]

--isArray#1: 连续数字键与 n 一致时返回 true 和最大下标
--isArray#2: 中途出现不可编码值立即返回 false
--isArray#3: 附加字符串键使其不是数组
local function encodable(value)
    local kind = type(value)
    return kind == "number" or kind == "string" or kind == "boolean" or kind == "nil"
end

local function isArray(t)
    local maxIndex = 0
    for k, v in pairs(t) do
        if type(k) == "number" and math.floor(k) == k and k >= 1 then
            if not encodable(v) then
                return false
            end
            maxIndex = math.max(maxIndex, k)
        elseif k == "n" then
            if v ~= #t then
                return false
            end
        elseif encodable(v) then
            return false
        end
    end
    return true, maxIndex
end

-- isArray#1
local ok, maxIndex = isArray({ [1] = "a", [2] = "b", [3] = "c", n = 3 })
assert(ok == true, "isArray#1 should accept contiguous array")
assert(maxIndex == 3, "isArray#1 maxIndex should be 3")
print("isArray#1", "ok", maxIndex)

-- isArray#1 空表也是数组
local okEmpty = isArray({})
assert(okEmpty == true, "isArray#1 should accept empty table")
print("isArray#1", "empty-ok")

-- isArray#2 数字键携带表值
local okBadValue = isArray({ [1] = "a", [2] = {}, n = 2 })
assert(okBadValue == false, "isArray#2 should reject table payload")
print("isArray#2", "rejected")

-- isArray#2 n 与实际元素数不一致
local okBadN = isArray({ [1] = "a", n = 5 })
assert(okBadN == false, "isArray#2 should reject mismatched n")
print("isArray#2", "rejected-n")

-- isArray#3 附加字符串键
local okExtra = isArray({ [1] = "a", n = 1, name = "extra" })
assert(okExtra == false, "isArray#3 should reject extra string key")
print("isArray#3", "rejected")

-- 全链路径在无序遍历下结论稳定
local mirror = { n = 4 }
for index = 1, 4 do mirror[index] = index * 2 end
local okMirror, maxMirror = isArray(mirror)
assert(okMirror == true and maxMirror == 4, "isArray#1 mirror array")
print("isArray#1", "mirror-ok", maxMirror)
