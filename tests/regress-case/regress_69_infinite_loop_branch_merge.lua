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
