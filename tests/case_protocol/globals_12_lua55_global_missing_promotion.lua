-- 先读取后写入的名字只保留可写声明；重复写不能改变首次写入顺序。
-- unluac: expect-contains [[global item4, item2]]
-- unluac: expect-contains [[global<const> item1, item3, item5, item6, print, assert]]
-- unluac: expect-count [[global item4, item2]] [[1]]
-- unluac: expect-count [[global<const> item1, item3, item5, item6, print, assert]] [[1]]
for i = 1, 6 do
    _ENV["item" .. i] = i
end

global marker = 0
local total = _ENV.item1 + _ENV.item2 + _ENV.item3 + _ENV.item4 + _ENV.item5 + _ENV.item6
_ENV.item4 = 40
_ENV.item2 = 20
_ENV.item4 = 41
_ENV.print("regress523", total, _ENV.item1, _ENV.item2, _ENV.item4, _ENV.item6)
_ENV.assert(total == 21 and _ENV.item2 == 20 and _ENV.item4 == 41)
