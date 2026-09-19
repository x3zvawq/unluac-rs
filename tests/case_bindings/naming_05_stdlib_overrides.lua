-- 库的显式改写不具有标准库签名身份；Luau 的只读标准库不支持本例的原地替换。
-- unluac: expect-contains [[os.date(a, b)]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[string.sub(a, b)]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:0]] [[a]] [[@proto=2]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:1]] [[b]] [[@proto=2]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:0]] [[a]] [[@proto=4]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:1]] [[b]] [[@proto=4]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
local saved = os.date
function os.date(x, y) return x + y end
function naming_replaced(a, b)
    return os.date(a, b)
end
local old_string = string
string = { sub = function(x, y) return x * y end }
function naming_changed(a, b)
    return string.sub(a, b)
end
assert(naming_replaced(4, 5) == 9)
assert(naming_changed(6, 7) == 42)
string = old_string
os.date = saved
