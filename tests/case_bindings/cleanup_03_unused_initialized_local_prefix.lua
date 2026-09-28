-- regress_376_unused_initialized_local_prefix: cleanup must not shift a live slot's return value
-- unluac: expect-contains [[, r0_]]

local function pair()
    return 17, 19
end

local dead, keep = pair()
assert(keep == 19)

-- 未读比较仍是原操作；后续宽常量池和构造器不能把它们当作可删前缀。
-- unluac: expect-count [[>= 1]] [[2]] [[@dialect=lua5.1]]
-- unluac: expect-count [[>= 2]] [[2]] [[@dialect=lua5.1]]
-- 满池后的数值比较仍应恢复读取与 LOADK 的相邻准备。
-- unluac: expect-contains [[.value < 0]]
-- unluac: expect-contains [[.optional.hidden]]
-- unluac: expect-contains [[.unused]]
local function arrays(left, right, state)
    -- 提前返回臂贡献常量；交换两臂会改变后续 RK 池边界。
    if state == nil then
        return "missing-input", "missing-state"
    else
        local first = left >= 2
        local unused_first = left >= 1
        local second = right >= 2
        local unused_second = right >= 1
        local result = {{value=first},{value=second}}
        -- 单次控制头消费者在很远的后缀；中间构造器仍需这个原槽声明。
        local delayed = (state.hidden or (state.optional and state.optional.hidden)) or false
        local unused = state.unused or false
        -- PUC 的常量 CONCAT 仍执行拼接，不能令后面的宽常量池证明失效。
        state.prefix = "pre" .. "fix"
        local constants = {
            1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009,
            1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019,
            1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029,
            1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039,
            1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049,
            1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059,
            1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069,
            1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079,
            1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089,
            1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099,
            1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109,
            1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119,
            1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129,
            1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139,
            1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149,
            1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159,
            1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169,
            1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179,
            1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189,
            1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199,
            1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209,
            1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219,
            1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229,
            1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239,
            1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249,
            1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259,
        }
        if state.value < 0 then
            state.value = state.value + math.pi * 2
        end
        if delayed then result[1].delayed = true end
        local saved_first, saved_second
        if state.copy then
            saved_first, saved_second = first, second
        end
        state.results[#state.results + 1] = {saved_first, saved_second, label = tostring(state.prefix)}
        return result, constants[260]
    end
end
-- unluac: expect-contains [[== nil then]]
local absent, reason = arrays(1, 2, nil)
assert(absent == "missing-input" and reason == "missing-state")
local state = {value = -1, optional = {hidden = true}, copy = true, results = {}}
local result, last = arrays(1,2,state)
assert(not result[1].value and result[2].value and last == 1259)
assert(state.value == -1 + math.pi * 2 and result[1].delayed and state.prefix == "prefix")
assert(state.results[1][1] == false and state.results[1][2] == true and state.results[1].label == "prefix")
state.copy = false
state.optional = nil
local again = arrays(1,2,state)
assert(state.value == -1 + math.pi * 2 and again[1].delayed == nil)
assert(state.results[2][1] == nil and state.results[2][2] == nil and state.results[2].label == "prefix")
state.hidden = true
assert(arrays(1,2,state)[1].delayed)

-- Decision 的 CurrentValue 终端沿用已有状态；不能新增无原槽的条件快照。
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=2]] [[@dialect=luajit]]
local function choose(node, defaults)
    local selected = node.selected
    if not selected then
        if node.kind == "one" then
            if defaults.selected then selected = defaults.selected end
        elseif node.kind == "two" then
            if defaults.selected then selected = defaults.selected end
        end
    end
    local values = {selected, node.tail}
    return values
end
local reads = 0
local defaults = setmetatable({}, {__index=function()
    reads = reads + 1
    return 31
end})
assert(choose({selected=17,kind="one",tail=9}, defaults)[1] == 17 and reads == 0)
assert(choose({kind="one",tail=9}, defaults)[1] == 31 and reads == 2)
assert(choose({selected=false,kind="two",tail=9}, defaults)[1] == 31 and reads == 4)
local missing = choose({kind="other",tail=9}, defaults)
assert(missing[1] == nil and missing[2] == 9 and reads == 4)
assert(choose({selected=false,kind="one"}, {selected=false})[1] == false)
