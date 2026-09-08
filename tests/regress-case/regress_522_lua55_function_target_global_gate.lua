-- 通配 gate 从首次全局访问开始，函数字段/方法 target 的根也属于读取。
-- unluac: expect-order [[global<const> *]] [[function box.f()]]
-- unluac: expect-not-contains [[global<const> box]]

box = { value = 11 }
local function run(flag)
    global marker = 0
    if flag then
        global<const> box, print
        function box.f() return 7 end
        function box:read() return self.value end
        print("target", box.f(), box:read())
    end
    return marker
end

run(true)
