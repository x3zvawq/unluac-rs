-- regress_197_long_bracket_control_byte#1: 含换行的字节串仍不能在 long-bracket 中裸写 NUL
-- unluac: expect-not-contains [[unluac error]]
local packed = "\000\n\020\000"
assert(#packed == 4)
assert(packed == string.char(0, 10, 20, 0))
