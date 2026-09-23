-- CALL 的单值结果与短路备用值共用原 CONCAT 操作数槽。
-- unluac: expect-not-contains [[= string.match]]
-- unluac: expect-contains [[.. (string.match(]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[return "<" .. (p5_0() and p5_1) .. ">"]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- unluac: expect-contains [[return "<" .. (call() and fallback) .. ">"]] [[@dialect=lua5.4]] [[@debug=retained]]
-- unluac: expect-contains [[print("regress_639_concat_call_fallback", r0_0("plain"), r0_1())]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- unluac: expect-contains [[print("regress_639_concat_call_fallback", handler("plain"), fallback_after_call())]] [[@dialect=lua5.4]] [[@debug=retained]]
-- unluac: expect-contains [[return "<" .. (r10_1() or r10_0) .. ">"]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- unluac: expect-contains [[return "<" .. (replace() or snapshot) .. ">"]] [[@dialect=lua5.4]] [[@debug=retained]]
local function handler(err)
    return "handled<" .. (string.match(err, "boom:[^>]+") or err) .. ">"
end
assert(handler("boom:bad") == "handled<boom:bad>")
assert(handler("plain") == "handled<plain>")

local function fallback_after_call()
    local fallback = "before"
    local count = 0
    local function lookup()
        fallback = "after"
        count = count + 1
        return false
    end
    local result = "<" .. (lookup() or fallback) .. ">"
    assert(count == 1)
    return result
end
assert(fallback_after_call() == "<after>")

local function choose_or(call, fallback)
    return "<" .. (call() or fallback) .. ">"
end
local function choose_and(call, fallback)
    return "<" .. (call() and fallback) .. ">"
end
assert(choose_or(function() return nil end, "nil") == "<nil>")
assert(choose_or(function() return 0, "ignored" end, "fallback") == "<0>")
assert(choose_and(function() return true end, "chosen") == "<chosen>")
assert(not pcall(choose_and, function() return false end, "unused"))
local function preserve_snapshot(value)
    local snapshot = value
    local function replace()
        value = "changed"
        return false
    end
    return "<" .. (replace() or snapshot) .. ">"
end
assert(preserve_snapshot("kept") == "<kept>")
local co = coroutine.create(function()
    return choose_or(function() return coroutine.yield("pause") end, "fallback")
end)
local ok, value = coroutine.resume(co)
assert(ok and value == "pause")
ok, value = coroutine.resume(co, false)
assert(ok and value == "<fallback>")
print("regress_639_concat_call_fallback", handler("plain"), fallback_after_call())
