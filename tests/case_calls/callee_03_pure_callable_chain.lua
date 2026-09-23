-- 布尔值拥有合法 __call；保留原本逐次写回的 NOT，不增加 callee 中转声明。
-- unluac: expect-count [[ = not ]] [[64]]
-- unluac: expect-ast-count [[local-binding]] [[3]]
local function check(value)
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 value=not value; value=not value; value=not value; value=not value
 if value() then return 1 else return 0 end
end
local count=0
local previous=debug.getmetatable(false)
debug.setmetatable(false,{__call=function(self) count=count+1; return self end})
assert(check(true)==1)
assert(check(false)==0)
assert(count==2)
debug.setmetatable(false,previous)
print("regress_550_pure_callable_chain", "OK")
