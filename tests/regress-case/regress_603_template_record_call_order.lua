-- 同键最后写常量时，Luau constant-pack 可能删除源码构造器中的早先调用。
-- 原分离写不能合并成 { a = event(), a = 5 } 并丢掉副作用。
local trace = ""
local function event(label, value)
    trace = trace .. label
    return value
end
local calls = { event }
local first = { a = calls[1]("first", 1) }
first.a = 5
assert(trace == "first" and first.a == 5)

-- 三个真实运行字段应按序保留，包括最后一次同键覆盖。
local second = {
    a = calls[1]("a", 2),
    b = calls[1]("b", 3),
    a = calls[1]("c", 4),
}
assert(trace == "firstabc" and second.a == 4 and second.b == 3)
print("record-call-order", trace, first.a, second.a, second.b)
