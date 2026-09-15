-- 原 O2 已内联的效果属于 caller；恢复原 factory 调用不能依赖再次内联。
-- NaN snapshot 抬高前缀后，第二次调用会跨 Luau 的寄存器压力上限。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
function make() return 1 end
function consume(x) total = total + x end
function barrier() end
function observe(label, tag)
    local count, vararg = debug.info(2, "a")
    local consistent = first_count == nil or (count == first_count and vararg == first_vararg)
    first_count, first_vararg = count, vararg
    print(label, tag, consistent)
    assert(consistent, "factory effects changed caller activation between identical sites")
end
local function opaque(x) return x end
local nan = opaque(0/0)
barrier()
local keep0, keep1, keep2, keep3, keep4, keep5, keep6, keep7 = make(), make(), make(), make(), make(), make(), make(), make()
local keep8, keep9, keep10, keep11, keep12, keep13, keep14, keep15 = make(), make(), make(), make(), make(), make(), make(), make()
local keep16, keep17, keep18, keep19, keep20, keep21, keep22, keep23 = make(), make(), make(), make(), make(), make(), make(), make()
local keep24, keep25, keep26, keep27, keep28, keep29, keep30, keep31 = make(), make(), make(), make(), make(), make(), make(), make()
local keep32, keep33, keep34, keep35, keep36, keep37, keep38, keep39 = make(), make(), make(), make(), make(), make(), make(), make()
local keep40, keep41, keep42, keep43, keep44, keep45, keep46, keep47 = make(), make(), make(), make(), make(), make(), make(), make()
local keep48, keep49, keep50, keep51, keep52, keep53, keep54, keep55 = make(), make(), make(), make(), make(), make(), make(), make()
local keep56, keep57, keep58, keep59, keep60, keep61, keep62, keep63 = make(), make(), make(), make(), make(), make(), make(), make()
local keep64, keep65, keep66, keep67, keep68, keep69, keep70, keep71 = make(), make(), make(), make(), make(), make(), make(), make()
local keep72, keep73, keep74, keep75, keep76, keep77, keep78, keep79 = make(), make(), make(), make(), make(), make(), make(), make()
local keep80, keep81, keep82, keep83, keep84, keep85, keep86, keep87 = make(), make(), make(), make(), make(), make(), make(), make()
local keep88, keep89, keep90, keep91, keep92, keep93, keep94, keep95 = make(), make(), make(), make(), make(), make(), make(), make()
local keep96, keep97, keep98, keep99, keep100, keep101, keep102, keep103 = make(), make(), make(), make(), make(), make(), make(), make()
local keep104, keep105, keep106, keep107, keep108, keep109, keep110, keep111 = make(), make(), make(), make(), make(), make(), make(), make()
local keep112, keep113, keep114, keep115, keep116, keep117, keep118, keep119 = make(), make(), make(), make(), make(), make(), make(), make()
local keep120, keep121, keep122 = make(), make(), make()
local function factory(tag)
    observe("activation-frame", tag)
    local function owner(...) return nan end
    return function() return owner() end
end
local first = factory("first")
local second = factory("second")
print("identity", first == second, first() ~= first(), second() ~= second())
total = 0
consume(keep0); consume(keep1); consume(keep2); consume(keep3); consume(keep4); consume(keep5); consume(keep6); consume(keep7)
consume(keep8); consume(keep9); consume(keep10); consume(keep11); consume(keep12); consume(keep13); consume(keep14); consume(keep15)
consume(keep16); consume(keep17); consume(keep18); consume(keep19); consume(keep20); consume(keep21); consume(keep22); consume(keep23)
consume(keep24); consume(keep25); consume(keep26); consume(keep27); consume(keep28); consume(keep29); consume(keep30); consume(keep31)
consume(keep32); consume(keep33); consume(keep34); consume(keep35); consume(keep36); consume(keep37); consume(keep38); consume(keep39)
consume(keep40); consume(keep41); consume(keep42); consume(keep43); consume(keep44); consume(keep45); consume(keep46); consume(keep47)
consume(keep48); consume(keep49); consume(keep50); consume(keep51); consume(keep52); consume(keep53); consume(keep54); consume(keep55)
consume(keep56); consume(keep57); consume(keep58); consume(keep59); consume(keep60); consume(keep61); consume(keep62); consume(keep63)
consume(keep64); consume(keep65); consume(keep66); consume(keep67); consume(keep68); consume(keep69); consume(keep70); consume(keep71)
consume(keep72); consume(keep73); consume(keep74); consume(keep75); consume(keep76); consume(keep77); consume(keep78); consume(keep79)
consume(keep80); consume(keep81); consume(keep82); consume(keep83); consume(keep84); consume(keep85); consume(keep86); consume(keep87)
consume(keep88); consume(keep89); consume(keep90); consume(keep91); consume(keep92); consume(keep93); consume(keep94); consume(keep95)
consume(keep96); consume(keep97); consume(keep98); consume(keep99); consume(keep100); consume(keep101); consume(keep102); consume(keep103)
consume(keep104); consume(keep105); consume(keep106); consume(keep107); consume(keep108); consume(keep109); consume(keep110); consume(keep111)
consume(keep112); consume(keep113); consume(keep114); consume(keep115); consume(keep116); consume(keep117); consume(keep118); consume(keep119)
consume(keep120); consume(keep121); consume(keep122)
print("total", total)
