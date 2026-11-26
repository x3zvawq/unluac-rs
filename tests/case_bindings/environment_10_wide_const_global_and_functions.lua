-- 覆盖 issue #41：主 chunk 常量表超过 255 项后，Lua 5.2+ 会先 `LOADK` 再 `GETTABUP`/`SETTABUP _ENV, rK`，
-- 需把寄存器键中的合法标识符字符串与直接 RK 常量一样还原为普通全局名与 `function M.name(...)` 声明，
-- 且顶层 local + 索引表构造器后的函数声明不得退化为临时变量或 `_ENV["..."]`。
-- unluac: expect-not-contains [[_ENV]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[function M.after_table(]] [[@dialect=luajit]]
-- unluac: expect-contains [[function LateGlobal.after_255(]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[function LateGlobal.after_255(]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[function LateGlobal.after_255(]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[function LateGlobal.after_255(]] [[@dialect=lua5.5]]

M = {}

local t1 = { 10 }
local t2 = { 20 }

-- 压入超过 255 个不同常量，确保后续新出现的全局名与字段名常量索引 > 255
local pad = {
    "k001", "k002", "k003", "k004", "k005", "k006", "k007", "k008", "k009", "k010",
    "k011", "k012", "k013", "k014", "k015", "k016", "k017", "k018", "k019", "k020",
    "k021", "k022", "k023", "k024", "k025", "k026", "k027", "k028", "k029", "k030",
    "k031", "k032", "k033", "k034", "k035", "k036", "k037", "k038", "k039", "k040",
    "k041", "k042", "k043", "k044", "k045", "k046", "k047", "k048", "k049", "k050",
    "k051", "k052", "k053", "k054", "k055", "k056", "k057", "k058", "k059", "k060",
    "k061", "k062", "k063", "k064", "k065", "k066", "k067", "k068", "k069", "k070",
    "k071", "k072", "k073", "k074", "k075", "k076", "k077", "k078", "k079", "k080",
    "k081", "k082", "k083", "k084", "k085", "k086", "k087", "k088", "k089", "k090",
    "k091", "k092", "k093", "k094", "k095", "k096", "k097", "k098", "k099", "k100",
    "k101", "k102", "k103", "k104", "k105", "k106", "k107", "k108", "k109", "k110",
    "k111", "k112", "k113", "k114", "k115", "k116", "k117", "k118", "k119", "k120",
    "k121", "k122", "k123", "k124", "k125", "k126", "k127", "k128", "k129", "k130",
    "k131", "k132", "k133", "k134", "k135", "k136", "k137", "k138", "k139", "k140",
    "k141", "k142", "k143", "k144", "k145", "k146", "k147", "k148", "k149", "k150",
    "k151", "k152", "k153", "k154", "k155", "k156", "k157", "k158", "k159", "k160",
    "k161", "k162", "k163", "k164", "k165", "k166", "k167", "k168", "k169", "k170",
    "k171", "k172", "k173", "k174", "k175", "k176", "k177", "k178", "k179", "k180",
    "k181", "k182", "k183", "k184", "k185", "k186", "k187", "k188", "k189", "k190",
    "k191", "k192", "k193", "k194", "k195", "k196", "k197", "k198", "k199", "k200",
    "k201", "k202", "k203", "k204", "k205", "k206", "k207", "k208", "k209", "k210",
    "k211", "k212", "k213", "k214", "k215", "k216", "k217", "k218", "k219", "k220",
    "k221", "k222", "k223", "k224", "k225", "k226", "k227", "k228", "k229", "k230",
    "k231", "k232", "k233", "k234", "k235", "k236", "k237", "k238", "k239", "k240",
    "k241", "k242", "k243", "k244", "k245", "k246", "k247", "k248", "k249", "k250",
    "k251", "k252", "k253", "k254", "k255", "k256", "k257", "k258", "k259", "k260",
}

function M.f1(a)
    return a + 1
end

function M.f2(a)
    return a + 2
end

M.Funs = {
    [1] = M.f1,
    [2] = M.f2,
}

function M.after_table(a, b)
    return a * b + t1[1] + t2[1]
end

LateGlobal = {}
LateCounter = 5

function LateGlobal.after_255(x)
    LateCounter = LateCounter + x
    return LateCounter
end

print(#pad, M.after_table(2, 3), M.Funs[2](1), LateGlobal.after_255(4))
