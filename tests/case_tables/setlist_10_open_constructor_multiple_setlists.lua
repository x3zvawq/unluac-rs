-- regress_432_open_constructor_multiple_setlists: a fixed SETLIST batch may precede the final open batch
-- unluac: expect-contains [[local r0_1 = {]] [[@dialect=lua5.4]]
-- unluac: expect-not-contains [[local r0_1 = {}]] [[@dialect=lua5.4]]
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[unluac error]]
local function tail()
    return 51, 52, 53
end

local values = {
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    tail(),
}

assert(#values == 53)
assert(values[1] == 1 and values[50] == 50)
assert(values[51] == 51 and values[52] == 52 and values[53] == 53)
print("regress_432_open_constructor_multiple_setlists", "ok")

-- 跨三批 SETLIST 的记录数组同时越过 RK 常量池边界；溢出的字段 LOADK 仍属于构造器。
-- unluac: expect-ast-count [[table-constructor]] [[139]]
-- unluac: expect-ast-count [[table-record-field]] [[265]]
-- unluac: expect-ast-count [[table-list-field]] [[183]]
local function build_records(catalog, state)
    arrayResetFirst, arrayResetSecond = nil, nil
    arrayAngle = 0.75 * math.pi
    arraySurplus = arrayAngle - math.pi * 0.5
    local records = {
        {score = 1, time = 0}, {score = 2, time = 1002}, {score = 3, time = 1003}, {score = 4, time = 1004},
        {score = 5, time = 1005}, {score = 6, time = 1006}, {score = 7, time = 1007}, {score = 8, time = 1008},
        {score = 9, time = 1009}, {score = 10, time = 1010}, {score = 11, time = 1011}, {score = 12, time = 1012},
        {score = 13, time = 1013}, {score = 14, time = 1014}, {score = 15, time = 1015}, {score = 16, time = 1016},
        {score = 17, time = 1017}, {score = 18, time = 1018}, {score = 19, time = 1019}, {score = 20, time = 1020},
        {score = 21, time = 1021}, {score = 22, time = 1022}, {score = 23, time = 1023}, {score = 24, time = 1024},
        {score = 25, time = 1025}, {score = 26, time = 1026}, {score = 27, time = 1027}, {score = 28, time = 1028},
        {score = 29, time = 1029}, {score = 30, time = 1030}, {score = 31, time = 1031}, {score = 32, time = 1032},
        {score = 33, time = 1033}, {score = 34, time = 1034}, {score = 35, time = 1035}, {score = 36, time = 1036},
        {score = 37, time = 1037}, {score = 38, time = 1038}, {score = 39, time = 1039}, {score = 40, time = 1040},
        {score = 41, time = 1041}, {score = 42, time = 1042}, {score = 43, time = 1043}, {score = 44, time = 1044},
        {score = 45, time = 1045}, {score = 46, time = 1046}, {score = 47, time = 1047}, {score = 48, time = 1048},
        {score = 49, time = 1049}, {score = 50, time = 1050}, {score = 51, time = 1051}, {score = 52, time = 1052},
        {score = 53, time = 1053}, {score = 54, time = 1054}, {score = 55, time = 1055}, {score = 56, time = 1056},
        {score = 57, time = 1057}, {score = 58, time = 1058}, {score = 59, time = 1059}, {score = 60, time = 1060},
        {score = 61, time = 1061}, {score = 62, time = 1062}, {score = 63, time = 1063}, {score = 64, time = 1064},
        {score = 65, time = 1065}, {score = 66, time = 1066}, {score = 67, time = 1067}, {score = 68, time = 1068},
        {score = 69, time = 1069}, {score = 70, time = 1070}, {score = 71, time = 1071}, {score = 72, time = 1072},
        {score = 73, time = 1073}, {score = 74, time = 1074}, {score = 75, time = 1075}, {score = 76, time = 1076},
        {score = 77, time = 1077}, {score = 78, time = 1078}, {score = 79, time = 1079}, {score = 80, time = 1080},
        {score = 81, time = 1081}, {score = 82, time = 1082}, {score = 83, time = 1083}, {score = 84, time = 1084},
        {score = 85, time = 1085}, {score = 86, time = 1086}, {score = 87, time = 1087}, {score = 88, time = 1088},
        {score = 89, time = 1089}, {score = 90, time = 1090}, {score = 91, time = 1091}, {score = 92, time = 1092},
        {score = 93, time = 1093}, {score = 94, time = 1094}, {score = 95, time = 1095}, {score = 96, time = 1096},
        {score = 97, time = 1097}, {score = 98, time = 1098}, {score = 99, time = 1099}, {score = 100, time = 1100},
        {score = 101, time = 1101}, {score = 102, time = 1102}, {score = 103, time = 1103}, {score = 104, time = 1104},
        {score = 105, time = 1105}, {score = 106, time = 1106}, {score = 107, time = 1107}, {score = 108, time = 1108},
        {score = 109, time = 1109}, {score = 110, time = 1110}, {score = 111, time = 1111}, {score = 112, time = 1112},
        {score = 113, time = 1113}, {score = 114, time = 1114}, {score = 115, time = 1115}, {score = 116, time = 1116},
        {score = 117, time = 1117}, {score = 118, time = 1118}, {score = 119, time = 1119}, {score = 120, time = 1120},
        {score = 121, time = 1121}, {score = 122, time = 1122}, {score = 123, time = 1123}, {score = 124, time = 1124},
        {score = 125, time = 1125}, {score = 126, time = 1126}, {score = 127, time = 1127}, {score = 128, time = 1128},
        {score = 129, time = 1129}, {score = 130, time = 0},
    }
    do
        local captured = records
        state.keep = function() return captured end
    end
    return records, {catalog.themes[state.theme].particles[1].name}
end
local catalog = {themes = {picked = {particles = {{name = "result"}}}}}
local state = {theme = "picked"}
local records, selected = build_records(catalog, state)
assert(arrayResetFirst == nil and arrayResetSecond == nil)
assert(arrayAngle > arraySurplus and arraySurplus > 0)
assert(state.keep() == records and selected[1] == "result")
local total = 0
for i, row in ipairs(records) do
    assert(row.score == i and row.time == ((i == 1 or i == 130) and 0 or 1000 + i))
    total = total + row.score
end
assert(#records == 130 and total == 8515)
print("multiple setlists with RK spills", #records, total)
