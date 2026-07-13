-- regress_139_lua55_contextual_global#1: global 在 Lua 5.5 标识符位置不是硬关键字
-- unluac: expect-contains [[global = 9]]
-- unluac: expect-not-contains [[_ENV]]
global = 9
print("regress_139_lua55_contextual_global#1", global)
