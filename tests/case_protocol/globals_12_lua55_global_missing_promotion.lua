-- 先读取后写入的全局访问与显式 global 声明在 Lua 5.5 中共存并保持语义一致。
-- unluac: expect-contains [[global *]]
-- unluac: expect-contains [[global marker = 0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]
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
_ENV.assert(_ENV.item1 == 1 and _ENV.item3 == 3 and _ENV.item5 == 5 and _ENV.item6 == 6)
