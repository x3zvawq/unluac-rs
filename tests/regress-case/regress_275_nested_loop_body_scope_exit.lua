-- regress_275_nested_loop_body_scope_exit: expanded nested body的内部core出口不能制造跨loop goto
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function(]]
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
print("regress_275_nested_loop_body_scope_exit")
