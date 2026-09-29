-- regress_125_luau_repeat_condition_side_effect#1: repeat 条件前的副作用不能被伪造的 continue 跳过
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[print]]
-- unluac: expect-not-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local subject = run()
-- unluac-runtime: local seen = {}
-- unluac-runtime: setfenv(subject, setmetatable({print = function(value) seen[#seen + 1] = value; assert(#seen <= 6, "observed repeat backedge") end}, {__index = getfenv()}))
-- unluac-runtime: assert(subject(true, false, false, {1, 2}) == 0)
-- unluac-runtime: assert(table.concat(seen, ",") == "0,0,0,0")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(subject(0, nil, nil, {1}) == 0)
-- unluac-runtime: assert(table.concat(seen, ",") == "0,0")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(subject(false, nil, true, {1, 2}) == 2)
-- unluac-runtime: assert(table.concat(seen, ",") == "1,2")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(subject(false, true, nil, {1, 2}) == 2)
-- unluac-runtime: assert(table.concat(seen, ",") == "1,2")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(subject(false, true, true, {}) == 0 and #seen == 0)
-- unluac-runtime: assert(not pcall(subject, false, false, true, {1, 2, 3}))
-- unluac-runtime: assert(table.concat(seen, ",") == "1,2,3,3,4,4,5")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(not pcall(subject, nil, 0, "", {1}))
-- unluac-runtime: assert(table.concat(seen, ",") == "0,0,0,0,0,0,0")
return function(c, a, b, t)
    local x = 0
    for _ in t do
        repeat
            if c then
                print(x)
            else
                if not a or not b then
                    x += 1
                    print(x)
                    if x < 3 then
                        break
                    end
                end
            end
            print(x)
        until c
    end
    return x
end
