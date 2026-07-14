-- unluac: expect-contains [[.m70(]]
-- unluac: expect-not-contains [[:m70()]]
local object = {}

for i = 1, 70 do
    object["m" .. i] = function(self)
        return i
    end
end

local function sink(...)
    local total = 0
    for i = 1, select("#", ...) do
        total = total + select(i, ...)
    end
    return total
end

local function run()
    return sink(
        object.m1(object), object.m2(object), object.m3(object), object.m4(object),
        object.m5(object), object.m6(object), object.m7(object), object.m8(object),
        object.m9(object), object.m10(object), object.m11(object), object.m12(object),
        object.m13(object), object.m14(object), object.m15(object), object.m16(object),
        object.m17(object), object.m18(object), object.m19(object), object.m20(object),
        object.m21(object), object.m22(object), object.m23(object), object.m24(object),
        object.m25(object), object.m26(object), object.m27(object), object.m28(object),
        object.m29(object), object.m30(object), object.m31(object), object.m32(object),
        object.m33(object), object.m34(object), object.m35(object), object.m36(object),
        object.m37(object), object.m38(object), object.m39(object), object.m40(object),
        object.m41(object), object.m42(object), object.m43(object), object.m44(object),
        object.m45(object), object.m46(object), object.m47(object), object.m48(object),
        object.m49(object), object.m50(object), object.m51(object), object.m52(object),
        object.m53(object), object.m54(object), object.m55(object), object.m56(object),
        object.m57(object), object.m58(object), object.m59(object), object.m60(object),
        object.m61(object), object.m62(object), object.m63(object), object.m64(object),
        object.m65(object), object.m66(object), object.m67(object), object.m68(object),
        object.m69(object), object.m70(object)
    )
end

print("regress_54_method_alias_wide_call_args", run())
