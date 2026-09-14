-- unluac: expect-contains [[local r1_2, r1_3 = coroutine.resume(r1_0)]]
-- unluac: expect-not-line [[local r1_2, r1_3]]

local function private_exit()
    local co = coroutine.create(function()
        coroutine.yield(10)
        coroutine.yield(20)
        return "done"
    end)
    local out = {}
    while true do
        local ok, value = coroutine.resume(co)
        if not ok or coroutine.status(co) == "dead" then
            out[#out + 1] = value or "nil"
            break
        end
        out[#out + 1] = value
    end
    return table.concat(out, ",")
end


assert(private_exit() == "10,20,done")
print("loop-private-exit-readability", private_exit())
