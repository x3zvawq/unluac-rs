-- regress_137_luajit_contextual_goto#1: goto 在 LuaJIT 标识符位置不是硬关键字
-- unluac: expect-contains [[goto = 7]]
-- unluac: expect-not-contains [[_ENV]]
goto = 7
print("regress_137_luajit_contextual_goto#1", goto)
