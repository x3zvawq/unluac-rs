-- regress_165_global_name_binding_shadow#1: debug 名不能遮蔽同函数内的全局引用
-- unluac: expect-contains [[function(print2)]]
-- unluac: expect-contains [[function methods.call(self2)]]
-- unluac: expect-not-contains [[function methods:call]]
-- unluac: expect-not-contains [[unluac error]]
-- 全局读写共用原 scratch 槽，不能因前一次 CALL 复用它而留下匿名中转。
-- unluac: expect-contains [[self = print]]
(function(print)
    _ENV.print("regress_165_global_name_binding_shadow#1", print)
end)(7)

-- regress_165_global_name_binding_shadow#2: 父绑定改名必须沿 capture provenance 传入闭包
local closure = (function(print)
    return function()
        _ENV.print("regress_165_global_name_binding_shadow#2", print)
    end
end)(8)
closure()

-- regress_165_global_name_binding_shadow#3: 冒号语法的隐式 self 不能遮蔽全局 self
_ENV.self = _ENV.print
local methods = { marker = 9 }
function methods:call()
    _ENV.self("regress_165_global_name_binding_shadow#3", self.marker)
end
methods:call()

-- sibling 的全局引用不能污染本函数的命名区间；此处 print 只引用参数。
-- unluac: expect-contains [[(print)]]
;(function(print)
    local function nested()
        return print + 1
    end
    assert(nested() == 10)
end)(9)
