-- regress_138_luau_contextual_continue#1: continue 在 Luau 标识符位置不是硬关键字
-- unluac: expect-contains [[continue = 8]]
-- unluac: expect-not-contains [[_ENV]]
continue = 8
print("regress_138_luau_contextual_continue#1", continue)
