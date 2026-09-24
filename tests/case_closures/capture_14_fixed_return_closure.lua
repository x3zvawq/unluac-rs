-- 固定返回区保留 COPY 与闭包创建的槽序，不把准备区变成额外 local。
-- unluac: expect-contains [[return read, function(]] [[@debug=retained]]
-- unluac: expect-ast-count [[do-block]] [[0]]
local function build(seed)
    local current = seed
    local function read()
        return current
    end
    return read, function(value)
        current = value
        return current
    end
end

local read, replace = build("first")
assert(read() == "first")
assert(replace("second") == "second")
assert(read() == "second")
print("fixed-return-closure", read())
