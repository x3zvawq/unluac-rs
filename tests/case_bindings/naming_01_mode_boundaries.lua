-- 同一 binding 的 NameMap 合同按模式及 debug 策略选择，不用字符串碰巧命中代替名字身份。
local data = { 10, 20 }
print(data[1], data[2], #data)
data[1] = data[2] + 1
assert(data[1] == 21)
