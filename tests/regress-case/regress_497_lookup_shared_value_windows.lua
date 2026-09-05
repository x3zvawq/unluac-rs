-- Copies share a value, but each physical home has an independent release endpoint.
local weak = setmetatable({}, { __mode = "v" })
local object = {}
weak[1] = object
object = nil
local a0 = weak[1]
local a1 = a0
local a2 = a1
local a3 = a2
local a4 = a3
local a5 = a4
local a6 = a5
local a7 = a6
local a8 = a7
local a9 = a8
local a10 = a9
local a11 = a10
local a12 = a11
local a13 = a12
local a14 = a13
local a15 = a14
local a16 = a15
local a17 = a16
local a18 = a17
local a19 = a18
local a20 = a19
local a21 = a20
local a22 = a21
local a23 = a22
local a24 = a23
local a25 = a24
local a26 = a25
local a27 = a26
local a28 = a27
local a29 = a28
local a30 = a29
local a31 = a30
collectgarbage("collect")
assert(weak[1] ~= nil)
a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30 = nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil
collectgarbage("collect")
assert(weak[1] ~= nil)
assert(a31 == weak[1])
a31 = nil
collectgarbage("collect")
assert(weak[1] == nil)
print("regress497", "released")
