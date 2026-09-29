-- 显式 false 入口与条件更新共享结果身份；七次潜在字段读取保留短路顺序。
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[15]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- LuaJIT 按子函数的逆序编号，seeded 对应 proto#4。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- 带来源的 NOT 与 CALL 属于同一短路返回帧，不能留下逐轮增长的载体链。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=luajit]]
local function seeded(flags)
    local result = false
    if not flags.a and not flags.b then
        if flags.c and flags.d then result = true
        elseif flags.e then result = true
        elseif flags.f and flags.g then result = true end
    end
    return result
end

local function reference(read)
    return not read("a") and not read("b")
        and (read("c") and read("d") or read("e") or read("f") and read("g"))
end

local hits = 0
-- 三种真假编码：Boolean、nil/0、false/空串；每组仍恰好命中 23 次。
for encoding = 0, 2 do
    for mask = 0, 127 do
        local values, bits = {}, mask
        for _, key in ipairs({ "a", "b", "c", "d", "e", "f", "g" }) do
            local bit = bits % 2 == 1
            if encoding == 0 then
                values[key] = bit
            elseif encoding == 1 then
                if bit then values[key] = 0 end
            else
                values[key] = bit and "" or false
            end
            bits = math.floor(bits / 2)
        end
        local expected_trace = ""
        local expected = reference(function(key)
            expected_trace = expected_trace .. key
            return values[key]
        end)
        local actual_trace = ""
        local actual = seeded(setmetatable({}, {
            __index = function(_, key)
                actual_trace = actual_trace .. key
                return values[key]
            end,
        }))
        if encoding == 0 then
            assert(actual == expected)
        else
            assert(actual == not not expected)
        end
        assert(type(actual) == "boolean")
        assert(select("#", seeded(values)) == 1)
        assert(actual_trace == expected_trace)
        if actual then hits = hits + 1 end
    end
    assert(hits == 23 * (encoding + 1))
end
assert(hits == 69)
print("boolean header seed", hits)
