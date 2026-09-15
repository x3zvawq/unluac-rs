-- regress_438_lua55_local_scope_crosses_global_decl: global syntax preserves the original call-frame prefix
-- unluac: expect-not-contains [[unluac error]]
-- 全局声明不占局部槽；后续 CALL 仍依赖全部原低槽，不能为180的预留目标提前缩域。
-- unluac: expect-ast-count [[local-decl]] [[40]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
-- unluac: expect-contains [[global slot_001]]
-- unluac: expect-contains [[global function exported_function]]

global marker = 0
global<const> boundary
global<const> assert, print
local original_assert = assert

local function run(p001, p002, p003, p004, p005, p006, p007, p008, p009, p010, p011, p012, p013, p014, p015, p016, p017, p018, p019, p020, p021, p022, p023, p024, p025, p026, p027, p028, p029, p030, p031, p032, p033, p034, p035, p036, p037, p038, p039, p040, p041, p042, p043, p044, p045, p046, p047, p048, p049, p050, p051, p052, p053, p054, p055, p056, p057, p058, p059, p060, p061, p062, p063, p064, p065, p066, p067, p068, p069, p070, p071, p072, p073, p074, p075, p076, p077, p078, p079, p080, p081, p082, p083, p084, p085, p086, p087, p088, p089, p090, p091, p092, p093, p094, p095, p096, p097, p098, p099, p100, p101, p102, p103, p104, p105, p106, p107, p108, p109, p110, p111, p112, p113, p114, p115, p116, p117, p118, p119, p120, p121, p122, p123, p124, p125, p126, p127, p128, p129, p130, p131, p132, p133, p134, p135, p136, p137, p138, p139, p140, p141, p142, p143, p144, p145)
    local value_001 = 1
    global assert
    assert = original_assert
    global boundary = value_001
    global slot_001 = value_001
    assert(value_001 == 1 and slot_001 == 1)
    local value_002 = 2
    global slot_002 = value_002
    assert(value_002 == 2 and slot_002 == 2)
    local value_003 = 3
    global slot_003 = value_003
    assert(value_003 == 3 and slot_003 == 3)
    local value_004 = 4
    global slot_004 = value_004
    assert(value_004 == 4 and slot_004 == 4)
    local value_005 = 5
    global slot_005 = value_005
    assert(value_005 == 5 and slot_005 == 5)
    local value_006 = 6
    global slot_006 = value_006
    assert(value_006 == 6 and slot_006 == 6)
    local value_007 = 7
    global slot_007 = value_007
    assert(value_007 == 7 and slot_007 == 7)
    local value_008 = 8
    global slot_008 = value_008
    assert(value_008 == 8 and slot_008 == 8)
    local value_009 = 9
    global slot_009 = value_009
    assert(value_009 == 9 and slot_009 == 9)
    local value_010 = 10
    global slot_010 = value_010
    assert(value_010 == 10 and slot_010 == 10)
    local value_011 = 11
    global slot_011 = value_011
    assert(value_011 == 11 and slot_011 == 11)
    local value_012 = 12
    global slot_012 = value_012
    assert(value_012 == 12 and slot_012 == 12)
    local value_013 = 13
    global slot_013 = value_013
    assert(value_013 == 13 and slot_013 == 13)
    local value_014 = 14
    global slot_014 = value_014
    assert(value_014 == 14 and slot_014 == 14)
    local value_015 = 15
    global slot_015 = value_015
    assert(value_015 == 15 and slot_015 == 15)
    local value_016 = 16
    global slot_016 = value_016
    assert(value_016 == 16 and slot_016 == 16)
    local value_017 = 17
    global slot_017 = value_017
    assert(value_017 == 17 and slot_017 == 17)
    local value_018 = 18
    global slot_018 = value_018
    assert(value_018 == 18 and slot_018 == 18)
    local value_019 = 19
    global slot_019 = value_019
    assert(value_019 == 19 and slot_019 == 19)
    local value_020 = 20
    global slot_020 = value_020
    global function exported_function(value)
        if value == 0 then
            return 0
        end
        return exported_function(value - 1) + 1
    end
    assert(value_020 == 20 and slot_020 == 20)
    local value_021 = 21
    global slot_021 = value_021
    assert(value_021 == 21 and slot_021 == 21)
    local value_022 = 22
    global slot_022 = value_022
    assert(value_022 == 22 and slot_022 == 22)
    local value_023 = 23
    global slot_023 = value_023
    assert(value_023 == 23 and slot_023 == 23)
    local value_024 = 24
    global slot_024 = value_024
    assert(value_024 == 24 and slot_024 == 24)
    local value_025 = 25
    global slot_025 = value_025
    assert(value_025 == 25 and slot_025 == 25)
    local value_026 = 26
    global slot_026 = value_026
    assert(value_026 == 26 and slot_026 == 26)
    local value_027 = 27
    global slot_027 = value_027
    assert(value_027 == 27 and slot_027 == 27)
    local value_028 = 28
    global slot_028 = value_028
    assert(value_028 == 28 and slot_028 == 28)
    local value_029 = 29
    global slot_029 = value_029
    assert(value_029 == 29 and slot_029 == 29)
    local value_030 = 30
    global slot_030 = value_030
    assert(value_030 == 30 and slot_030 == 30)
    local value_031 = 31
    global slot_031 = value_031
    assert(value_031 == 31 and slot_031 == 31)
    local value_032 = 32
    global slot_032 = value_032
    assert(value_032 == 32 and slot_032 == 32)
    local value_033 = 33
    global slot_033 = value_033
    assert(value_033 == 33 and slot_033 == 33)
    local value_034 = 34
    global slot_034 = value_034
    assert(value_034 == 34 and slot_034 == 34)
    local value_035 = 35
    global slot_035 = value_035
    assert(value_035 == 35 and slot_035 == 35)
    boundary = 2
    assert(boundary == 2)
    local value_036 = 36
    global slot_036 = value_036
    assert(value_036 == 36 and slot_036 == 36)
    local value_037 = 37
    global slot_037 = value_037
    assert(value_037 == 37 and slot_037 == 37)
    local value_038 = 38
    global slot_038 = value_038
    assert(value_038 == 38 and slot_038 == 38)
    local value_039 = 39
    global slot_039 = value_039
    assert(value_039 == 39 and slot_039 == 39)
    local value_040 = 40
    global slot_040 = value_040
    assert(value_040 == 40 and slot_040 == 40)
    assert(exported_function(8) == 8)
    assert = original_assert
end

run()
print("regress_438_lua55_local_scope_crosses_global_decl", "OK")
