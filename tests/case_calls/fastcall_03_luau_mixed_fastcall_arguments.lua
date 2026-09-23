-- 同一 FASTCALL 的常量参数与 fallback COPY 必须共同恢复，不每轮再造参数 local。
-- unluac: expect-count [[math.max(]] [[2]]
-- unluac: expect-ast-max [[local-decl]] [[4]] [[@proto=2]]
-- unluac: expect-not-contains [[ = false]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@proto=0]]
local function check(value)
    local positive = value > 0
    assert(positive, "positive input required")
    local maximum = math.max(value, 5)
    assert(maximum >= value and maximum >= 5)
    print("mixed", positive, maximum)
end
local calls = { check }
calls[1](7)
getfenv(0)
calls[1](3)

-- 有事件的 direct 参数不在常量证明内；先读取 value，再调用 setter，保持原快照。
local function changing_argument()
    local value = 2
    local function change()
        value = 7
        return 5
    end
    local setters = { change }
    local maximum = math.max(value, setters[1]())
    assert(maximum == 5 and value == 7)
    print("snapshot", maximum, value)
end
changing_argument()
