-- 作用域末端的 debug local 即使区间为空，也保留声明及初始化结果身份。
-- unluac: expect-contains [[local BadConfig = load_config("single")]] [[@debug=retained]]
-- unluac: expect-contains [[local Left, Right = pair()]] [[@debug=retained]]
-- unluac: expect-contains [[local Tail = load_config("nested")]] [[@debug=retained]]
-- unluac: expect-contains [[local Last = ]] [[@debug=retained]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=5]] [[@dialect=lua5.4]] [[@debug=retained]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=5]] [[@dialect=lua5.5]] [[@debug=retained]]
local events = {}
function load_config(name)
    events[#events + 1] = name
    return {name = name}
end
function pair()
    events[#events + 1] = "pair"
    return false, nil
end
local function single()
    local BadConfig = load_config("single")
end
local function multiple()
    local Left, Right = pair()
end
local function nested()
    do
        local Outer = load_config("outer")
        print(Outer.name)
        local Tail = load_config("nested")
    end
    local Last = load_config("after")
end
single()
multiple()
nested()
assert(table.concat(events, ",") == "single,pair,outer,nested,after")
print(table.concat(events, ","))
