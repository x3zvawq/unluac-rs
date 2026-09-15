-- 嵌套闭包含真实调用时，AST build 不能按 proto 深度递归构造子函数体。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[64]]
local chain = function()
    print("layer", 0)
return function()
    print("layer", 1)
return function()
    print("layer", 2)
return function()
    print("layer", 3)
return function()
    print("layer", 4)
return function()
    print("layer", 5)
return function()
    print("layer", 6)
return function()
    print("layer", 7)
return function()
    print("layer", 8)
return function()
    print("layer", 9)
return function()
    print("layer", 10)
return function()
    print("layer", 11)
return function()
    print("layer", 12)
return function()
    print("layer", 13)
return function()
    print("layer", 14)
return function()
    print("layer", 15)
return function()
    print("layer", 16)
return function()
    print("layer", 17)
return function()
    print("layer", 18)
return function()
    print("layer", 19)
return function()
    print("layer", 20)
return function()
    print("layer", 21)
return function()
    print("layer", 22)
return function()
    print("layer", 23)
return function()
    print("layer", 24)
return function()
    print("layer", 25)
return function()
    print("layer", 26)
return function()
    print("layer", 27)
return function()
    print("layer", 28)
return function()
    print("layer", 29)
return function()
    print("layer", 30)
return function()
    print("layer", 31)
return function()
    print("layer", 32)
return function()
    print("layer", 33)
return function()
    print("layer", 34)
return function()
    print("layer", 35)
return function()
    print("layer", 36)
return function()
    print("layer", 37)
return function()
    print("layer", 38)
return function()
    print("layer", 39)
return function()
    print("layer", 40)
return function()
    print("layer", 41)
return function()
    print("layer", 42)
return function()
    print("layer", 43)
return function()
    print("layer", 44)
return function()
    print("layer", 45)
return function()
    print("layer", 46)
return function()
    print("layer", 47)
return function()
    print("layer", 48)
return function()
    print("layer", 49)
return function()
    print("layer", 50)
return function()
    print("layer", 51)
return function()
    print("layer", 52)
return function()
    print("layer", 53)
return function()
    print("layer", 54)
return function()
    print("layer", 55)
return function()
    print("layer", 56)
return function()
    print("layer", 57)
return function()
    print("layer", 58)
return function()
    print("layer", 59)
return function()
    print("layer", 60)
return function()
    print("layer", 61)
return function()
    print("layer", 62)
return function()
    print("layer", 63)
return 123
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
for index = 1, 64 do
    assert(type(chain) == "function")
    chain = chain()
end
assert(chain == 123)
print("regress_491_nested_closure_bodies", "OK")
