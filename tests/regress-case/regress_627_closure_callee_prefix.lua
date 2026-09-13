-- 第三个调用仍须复用原 callee COPY，重编译不能逐轮增加中转声明。
local function f0()
    print("0a")
    print("0b")
end
f0()
local function f1()
    print("1a")
    print("1b")
end
f1()
local function f2()
    print("2a")
    print("2b")
end
f2()
