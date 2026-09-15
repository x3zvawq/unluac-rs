-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[if r0_2 and #r0_0 ~= 0 and r0_1.queue then]]
-- unluac: expect-contains [[coroutine.yield()]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

local queue = {}
local server = {}
local credentials

local function run()
    while true do
        if credentials and #queue ~= 0 and server.queue then
            local request = table.remove(queue)
            consume(server.region, server.queue, request)
        else
            coroutine.yield()
        end
    end
end

-- 保留无限循环，通过它已有的 yield 边界逐步观察，无需依赖超时终止。
local log = {}
function consume(region, name, request)
    assert(region == "region" and name == "jobs")
    log[#log + 1] = request
end
local worker = coroutine.create(run)
assert(coroutine.resume(worker))
assert(coroutine.status(worker) == "suspended" and #log == 0)
queue[1], queue[2] = "first", "second"
server.region, server.queue = "region", "jobs"
assert(coroutine.resume(worker))
assert(#log == 0 and #queue == 2)
credentials = true
server.queue = nil
assert(coroutine.resume(worker))
assert(#log == 0 and #queue == 2)
server.queue = "jobs"
assert(coroutine.resume(worker))
assert(#queue == 0 and table.concat(log, ",") == "second,first")
queue[1] = "third"
assert(coroutine.resume(worker))
assert(#queue == 0 and table.concat(log, ",") == "second,first,third")
assert(coroutine.status(worker) == "suspended")
print("regress_69#1", table.concat(log, ","))
