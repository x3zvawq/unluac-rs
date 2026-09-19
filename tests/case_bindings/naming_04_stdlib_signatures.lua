-- 实参角色只在 heuristic 下参与命名，且不覆盖 debug 或业务字段提供的更具体名字。
-- unluac: expect-name [[local:0]] [[format]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[local:1]] [[time]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[local:0]] [[fmt]] [[@debug=retained]] [[@dialect=lua5.4]]
-- unluac: expect-name [[local:1]] [[epoch]] [[@debug=retained]] [[@dialect=lua5.4]]
-- unluac: expect-name [[local:1]] [[fmt]] [[@debug=retained]] [[@dialect=luau]]
-- unluac: expect-name [[local:2]] [[epoch]] [[@debug=retained]] [[@dialect=luau]]
-- unluac: expect-contains [[local fmt, epoch]] [[@debug=retained]]
-- unluac: expect-name [[local:0]] [[value]] [[@naming-mode=simple]] [[@debug=stripped]] [[@dialect=lua5.4]]
-- unluac: expect-name [[local:0]] [[r0_0]] [[@naming-mode=debug-like]] [[@debug=stripped]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[(text, start_index, end_index)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[(list, value)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[(list, position, value)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[string.sub(a, 1), string.find("abc", a)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[string.find("abc", a), string.sub(a, 1)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[(message)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[table.insert(a, b())]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-contains [[(text, pattern, start_index, plain)]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[param:0]] [[a]] [[@proto=11]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[param:1]] [[b]] [[@proto=11]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[param:0]] [[a]] [[@proto=13]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]] [[@debug=stripped]]
-- unluac: expect-name [[param:1]] [[b]] [[@proto=13]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]] [[@debug=stripped]]
function naming_inputs() return "!%Y", 946684800 end
local fmt, epoch = naming_inputs()
print(fmt, epoch, os.date(fmt, epoch))
assert(os.date(fmt, epoch) == "2000")

function naming_slice(a, b, c)
    local part = string.sub(a, b, c)
    print(part)
    return part
end
function naming_append(a, b)
    table.insert(a, b)
    return a[1]
end
function naming_insert(a, b, c)
    table.insert(a, b, c)
    return a[b]
end
function naming_conflicting(a)
    print(string.sub(a, 1), string.find("abc", a))
    return a
end
function naming_conflicting_reverse(a)
    print(string.find("abc", a), string.sub(a, 1))
    return a
end
function naming_priority(a)
    local out = { message = a }
    print(string.sub(a, 1), out.message)
    return out.message
end
function naming_open(a, b)
    -- 开放尾调用宽度未知，不能猜 table.insert 使用两个还是三个实参。
    table.insert(a, b())
    return a[1]
end
function naming_find(a, b, c, d)
    return string["find"](a, b, c, d)
end
assert(naming_slice("abcdef", 2, 4) == "bcd")
assert(naming_append({}, 7) == 7)
assert(naming_insert({}, 1, 8) == 8)
assert(naming_conflicting("b") == "b")
assert(naming_conflicting_reverse("b") == "b")
assert(naming_priority("message") == "message")
assert(naming_open({}, function() return 1, 9 end) == 9)
local first, last = naming_find("abc", "b", 1, true)
assert(first == 2 and last == 2)

-- 这些反例与正向库调用共存，防止库写入的整模块排除掩盖局部身份判断。
function naming_shadow(a, b)
    local os = { date = function(x, y) return x + y end }
    return os.date(a, b)
end
local alias = string.sub
function naming_alias(a, b)
    assert(alias == string.sub)
    return alias(a, b)
end
assert(naming_shadow(2, 3) == 5)
assert(naming_alias("hello", 2) == "ello")
