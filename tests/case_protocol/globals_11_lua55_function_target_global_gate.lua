-- 通配 gate 从首次全局访问开始，函数字段/方法 target 的根也属于读取。
-- unluac: expect-order [[global<const> *]] [[function box.f()]]
-- unluac: expect-not-contains [[global<const> box]]
-- unluac: expect-count [[global<const> *]] [[1]]
-- unluac: expect-contains [[function box:read()]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=0]]

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

assert(run(false) == 0 and box.f == nil and box.read == nil)
_ENV.marker = nil
assert(run(true) == 0 and box.f() == 7 and box:read() == 11)
box.value = 17
assert(box:read() == 17)
