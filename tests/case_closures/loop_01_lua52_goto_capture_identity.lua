-- regress_272_lua52_goto_capture_identity: backward goto 不能把共享 capture 槽降成逐轮 local
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local functions = {}
local value

::again::
value = #functions + 1
functions[#functions + 1] = function()
    return value
end
if #functions < 2 then
    goto again
end

assert(functions[1]() == 2)
assert(functions[2]() == 2)
print("regress_272_lua52_goto_capture_identity")
