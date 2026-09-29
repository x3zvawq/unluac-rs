-- regress_122_luau_same_header_loop_break_owner#1: same-header loop 的条件 header 不被前置短路吞并
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- break 与外层 repeat 条件合成同一短路退出条件，保留两层循环。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local subject = run()
-- unluac-runtime: local seen = {}
-- unluac-runtime: setfenv(subject, setmetatable({print = function(k, v) seen[#seen + 1] = k .. ":" .. v end}, {__index = getfenv()}))
-- unluac-runtime: assert(subject(true, false, {11, 22}) == true)
-- unluac-runtime: assert(table.concat(seen, ",") == "1:11,2:22")
-- unluac-runtime: seen = {}
-- unluac-runtime: assert(subject(0, nil, {}) == true and #seen == 0)
-- unluac-runtime: assert(subject("", false, {33}) == true)
-- unluac-runtime: assert(table.concat(seen, ",") == "1:33")
return function(a, b, xs)
    repeat
        repeat
            for k, v in xs do
                print(k, v)
            end
        until not b
        if a and b then break end
    until a
    return true
end
