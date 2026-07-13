-- regress_132_luajit_infinite_imaginary#1: 非有限虚部必须保持合法 numeric-token suffix
-- unluac: expect-contains [[1e999i]]
-- unluac: expect-contains [[-1e999i]]
-- unluac: expect-not-contains [[(1/0)i]]
return 1e999i, -1e999i
