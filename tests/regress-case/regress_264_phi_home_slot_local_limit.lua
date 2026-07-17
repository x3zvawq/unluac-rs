-- regress_264_phi_home_slot_local_limit#1: 顺序branch phi必须复用同一物理home slot
-- unluac: expect-not-contains [[local r1_1]]
local function run(flags)
    local value = 0
    if flags[1] then value = value + 0 end if flags[2] then value = value + 0 end if flags[3] then value = value + 0 end if flags[4] then value = value + 0 end
    if flags[5] then value = value + 0 end if flags[6] then value = value + 0 end if flags[7] then value = value + 0 end if flags[8] then value = value + 0 end
    if flags[9] then value = value + 0 end if flags[10] then value = value + 0 end if flags[11] then value = value + 0 end if flags[12] then value = value + 0 end
    if flags[13] then value = value + 0 end if flags[14] then value = value + 0 end if flags[15] then value = value + 0 end if flags[16] then value = value + 0 end
    if flags[17] then value = value + 0 end if flags[18] then value = value + 0 end if flags[19] then value = value + 0 end if flags[20] then value = value + 0 end
    if flags[21] then value = value + 0 end if flags[22] then value = value + 0 end if flags[23] then value = value + 0 end if flags[24] then value = value + 0 end
    if flags[25] then value = value + 0 end if flags[26] then value = value + 0 end if flags[27] then value = value + 0 end if flags[28] then value = value + 0 end
    if flags[29] then value = value + 0 end if flags[30] then value = value + 0 end if flags[31] then value = value + 0 end if flags[32] then value = value + 0 end
    if flags[33] then value = value + 0 end if flags[34] then value = value + 0 end if flags[35] then value = value + 0 end if flags[36] then value = value + 0 end
    if flags[37] then value = value + 0 end if flags[38] then value = value + 0 end if flags[39] then value = value + 0 end if flags[40] then value = value + 0 end
    if flags[41] then value = value + 0 end if flags[42] then value = value + 0 end if flags[43] then value = value + 0 end if flags[44] then value = value + 0 end
    if flags[45] then value = value + 0 end if flags[46] then value = value + 0 end if flags[47] then value = value + 0 end if flags[48] then value = value + 0 end
    if flags[49] then value = value + 0 end if flags[50] then value = value + 0 end if flags[51] then value = value + 0 end if flags[52] then value = value + 0 end
    if flags[53] then value = value + 0 end if flags[54] then value = value + 0 end if flags[55] then value = value + 0 end if flags[56] then value = value + 0 end
    if flags[57] then value = value + 0 end if flags[58] then value = value + 0 end if flags[59] then value = value + 0 end if flags[60] then value = value + 0 end
    if flags[61] then value = value + 0 end if flags[62] then value = value + 0 end if flags[63] then value = value + 0 end if flags[64] then value = value + 0 end
    if flags[65] then value = value + 0 end if flags[66] then value = value + 0 end if flags[67] then value = value + 0 end if flags[68] then value = value + 0 end
    if flags[69] then value = value + 0 end if flags[70] then value = value + 0 end if flags[71] then value = value + 0 end if flags[72] then value = value + 0 end
    if flags[73] then value = value + 0 end if flags[74] then value = value + 0 end if flags[75] then value = value + 0 end if flags[76] then value = value + 0 end
    if flags[77] then value = value + 0 end if flags[78] then value = value + 0 end if flags[79] then value = value + 0 end if flags[80] then value = value + 0 end
    if flags[81] then value = value + 0 end if flags[82] then value = value + 0 end if flags[83] then value = value + 0 end if flags[84] then value = value + 0 end
    if flags[85] then value = value + 0 end if flags[86] then value = value + 0 end if flags[87] then value = value + 0 end if flags[88] then value = value + 0 end
    if flags[89] then value = value + 0 end if flags[90] then value = value + 0 end if flags[91] then value = value + 0 end if flags[92] then value = value + 0 end
    if flags[93] then value = value + 0 end if flags[94] then value = value + 0 end if flags[95] then value = value + 0 end if flags[96] then value = value + 0 end
    if flags[97] then value = value + 0 end if flags[98] then value = value + 0 end if flags[99] then value = value + 0 end if flags[100] then value = value + 0 end
    if flags[101] then value = value + 0 end if flags[102] then value = value + 0 end if flags[103] then value = value + 0 end if flags[104] then value = value + 0 end
    if flags[105] then value = value + 0 end if flags[106] then value = value + 0 end if flags[107] then value = value + 0 end if flags[108] then value = value + 0 end
    if flags[109] then value = value + 0 end if flags[110] then value = value + 0 end if flags[111] then value = value + 0 end if flags[112] then value = value + 0 end
    if flags[113] then value = value + 0 end if flags[114] then value = value + 0 end if flags[115] then value = value + 0 end if flags[116] then value = value + 0 end
    if flags[117] then value = value + 0 end if flags[118] then value = value + 0 end if flags[119] then value = value + 0 end if flags[120] then value = value + 0 end
    if flags[121] then value = value + 0 end if flags[122] then value = value + 0 end if flags[123] then value = value + 0 end if flags[124] then value = value + 0 end
    if flags[125] then value = value + 0 end if flags[126] then value = value + 0 end if flags[127] then value = value + 0 end if flags[128] then value = value + 0 end
    if flags[129] then value = value + 0 end if flags[130] then value = value + 0 end if flags[131] then value = value + 0 end if flags[132] then value = value + 0 end
    if flags[133] then value = value + 0 end if flags[134] then value = value + 0 end if flags[135] then value = value + 0 end if flags[136] then value = value + 0 end
    if flags[137] then value = value + 0 end if flags[138] then value = value + 0 end if flags[139] then value = value + 0 end if flags[140] then value = value + 0 end
    if flags[141] then value = value + 0 end if flags[142] then value = value + 0 end if flags[143] then value = value + 0 end if flags[144] then value = value + 0 end
    if flags[145] then value = value + 0 end if flags[146] then value = value + 0 end if flags[147] then value = value + 0 end if flags[148] then value = value + 0 end
    if flags[149] then value = value + 0 end if flags[150] then value = value + 0 end if flags[151] then value = value + 0 end if flags[152] then value = value + 0 end
    if flags[153] then value = value + 0 end if flags[154] then value = value + 0 end if flags[155] then value = value + 0 end if flags[156] then value = value + 0 end
    if flags[157] then value = value + 0 end if flags[158] then value = value + 0 end if flags[159] then value = value + 0 end if flags[160] then value = value + 0 end
    if flags[161] then value = value + 0 end if flags[162] then value = value + 0 end if flags[163] then value = value + 0 end if flags[164] then value = value + 0 end
    if flags[165] then value = value + 0 end if flags[166] then value = value + 0 end if flags[167] then value = value + 0 end if flags[168] then value = value + 0 end
    if flags[169] then value = value + 0 end if flags[170] then value = value + 0 end if flags[171] then value = value + 0 end if flags[172] then value = value + 0 end
    if flags[173] then value = value + 0 end if flags[174] then value = value + 0 end if flags[175] then value = value + 0 end if flags[176] then value = value + 0 end
    if flags[177] then value = value + 0 end if flags[178] then value = value + 0 end if flags[179] then value = value + 0 end if flags[180] then value = value + 0 end
    if flags[181] then value = value + 0 end if flags[182] then value = value + 0 end if flags[183] then value = value + 0 end if flags[184] then value = value + 0 end
    if flags[185] then value = value + 0 end if flags[186] then value = value + 0 end if flags[187] then value = value + 0 end if flags[188] then value = value + 0 end
    if flags[189] then value = value + 0 end if flags[190] then value = value + 0 end if flags[191] then value = value + 0 end if flags[192] then value = value + 0 end
    if flags[193] then value = value + 0 end if flags[194] then value = value + 0 end if flags[195] then value = value + 0 end if flags[196] then value = value + 0 end
    if flags[197] then value = value + 0 end if flags[198] then value = value + 0 end if flags[199] then value = value + 0 end if flags[200] then value = value + 0 end
    return value
end

print("regress_264_phi_home_slot_local_limit#1", run({}))

