-- OPEN 参数尾包是循环条件的依赖，不能把内层 CALL 错当成 repeat 正文。
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-not-contains [[ = accept]]
-- unluac: expect-not-contains [[while true do]]
local events = {}
local remaining = 0
local function head()
    events[#events + 1] = "head"
    return 5
end
local function pair()
    events[#events + 1] = "pair"
    return 7, "tail"
end
local function accept(first, value, tail)
    events[#events + 1] = "accept"
    assert(first == 5 and value == 7 and tail == "tail")
    remaining = remaining - 1
    if remaining < 0 then return 0 end
    return 12
end
local function run(limit)
    local count = 0
    while accept(head(), pair()) == 12 do
        count = count + 1
        if count == limit then break end
    end
    return count
end

remaining = 4
assert(run(2) == 2 and remaining == 2)
assert(table.concat(events, ",") == "head,pair,accept,head,pair,accept")
events = {}
remaining = 2
assert(run(9) == 2 and remaining == -1)
assert(table.concat(events, ",") == "head,pair,accept,head,pair,accept,head,pair,accept")
events = {}
remaining = 0
assert(run(2) == 0 and remaining == -1)
assert(table.concat(events, ",") == "head,pair,accept")
print("open_call_condition", "OK")
