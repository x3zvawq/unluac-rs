-- regress_132_luajit_infinite_imaginary#1: 非有限虚部必须保持合法 numeric-token suffix
-- unluac: expect-contains [[1e999i]]
-- unluac: expect-contains [[-1e999i]]
-- unluac: expect-not-contains [[(1/0)i]]
local positive, negative = 1e999i, -1e999i
assert(positive.re == 0 and negative.re == 0)
assert(positive.im == math.huge and negative.im == -math.huge)
print("regress_132#1", positive.re, positive.im, negative.re, negative.im)
return positive, negative
