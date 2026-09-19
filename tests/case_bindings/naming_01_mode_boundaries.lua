-- 同一 binding 的 NameMap 合同按模式及 debug 策略选择，不用字符串碰巧命中代替名字身份。
-- unluac: expect-name [[local:0]] [[r0_0]] [[@naming-mode=debug-like]] [[@debug=stripped]] [[@dialect=lua5.4]]
-- unluac: expect-name [[local:0]] [[value]] [[@naming-mode=simple]] [[@debug=stripped]] [[@dialect=lua5.4]]
-- unluac: expect-name [[local:0]] [[r0_1]] [[@naming-mode=debug-like]] [[@debug=stripped]] [[@dialect=lua5.5]]
-- unluac: expect-name [[local:0]] [[value2]] [[@naming-mode=simple]] [[@debug=stripped]] [[@dialect=lua5.5]]
-- unluac: expect-name [[local:0]] [[arr]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[local:0]] [[data]] [[@debug=retained]]
-- unluac: expect-name [[local:0]] [[arr]] [[@naming-mode=heuristic]] [[@debug=ignored]]
-- unluac: expect-ast-count [[table-constructor]] [[1]]
local data = { 10, 20 }
print(data[1], data[2], #data)
data[1] = data[2] + 1
assert(data[1] == 21)
