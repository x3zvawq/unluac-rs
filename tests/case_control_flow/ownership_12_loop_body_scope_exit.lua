-- regress_275_nested_loop_body_scope_exit: expanded nested body的内部core出口不能制造跨loop goto
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function(]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
local function run(a, b, c, xs)
    for key in pairs(xs) do
        repeat
            if a then
                print(a)
            else
                for index = 1, 1 do
                    print(index)
                    break
                end
                if c then
                    print(1)
                    break
                else
                    print(2)
                    break
                end
            end
        until c
    end
end

run(false, false, false, { true })
local saved_print = print
local trace = {}
print = function(value)
    trace[#trace + 1] = value
    assert(#trace <= 6, "repeat did not exit")
end
run(true, false, true, {true, true})
assert(#trace == 2 and trace[1] == true and trace[2] == true)
trace = {}
run(false, true, true, {true, true})
assert(table.concat(trace, ",") == "1,1,1,1")
trace = {}
run(false, false, false, {true, true})
assert(table.concat(trace, ",") == "1,2,1,2")
trace = {}
run(0, false, "", {true, true})
assert(#trace == 2 and trace[1] == 0 and trace[2] == 0)
trace = {}
run(true, false, false, {})
assert(#trace == 0)
-- 假尾条件确实回到 repeat 正文，由观察器在第七次打印时终止这条无限路径。
assert(not pcall(run, true, false, false, {true}))
assert(#trace == 7 and trace[1] == true and trace[7] == true)
print = saved_print
print("regress_275_nested_loop_body_scope_exit")
