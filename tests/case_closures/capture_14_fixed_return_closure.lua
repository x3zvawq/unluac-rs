-- 固定返回区保留 COPY 与闭包创建的槽序，不把准备区变成额外 local。
-- unluac: expect-contains [[return read, function(]] [[@debug=retained]]
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

local other_read, other_replace = build(false)
assert(read ~= other_read and replace ~= other_replace)
assert(other_read() == false and read() == "second")
assert(replace(nil) == nil and read() == nil)
assert(other_replace(17) == 17 and other_read() == 17 and read() == nil)
