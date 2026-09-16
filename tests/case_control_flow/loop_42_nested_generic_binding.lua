-- generic-for 可见 binding 在内层 numeric-for 中重赋值，隐藏 control 仍由外层协议持有。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=lua5.1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=lua5.2]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.3]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=lua5.3]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.5]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=lua5.5]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=luajit]] [[@proto=5]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=luajit]] [[@proto=5]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
local A = {}

function A:init()
  local B = {}
  for i, v in pairs(B) do
    for _2 = 1, 200 do
      if G[v.id].next == 0 then
        v = {id = -1}
        B[i] = v
      end
    end
  end
end

-- 用可替换的 pairs 给原样例的空 B 注入数据，确保真正执行两层循环。
local saved_pairs = pairs
local mode, current, first, second
local queries, iterator_calls, last_control
pairs = function(tbl)
    current = tbl
    first, second = { id = 1 }, { id = 2 }
    if mode ~= "empty" then
        tbl[1], tbl[2] = first, second
    end
    return function(state, control)
        assert(state == current and control == last_control)
        iterator_calls = iterator_calls + 1
        local key = control + 1
        if state[key] then
            last_control = key
            return key, state[key]
        end
    end, tbl, 0
end
G = setmetatable({}, { __index = function(_, id)
    queries[id] = (queries[id] or 0) + 1
    if (id == 1 and mode ~= "stable") or (id == -1 and mode == "repeat-update") then
        return { next = 0 }
    end
    return { next = 1 }
end })
local function run(selected)
    mode = selected
    queries, iterator_calls, last_control = {}, 0, 0
    A:init()
    if mode == "empty" then
        assert(iterator_calls == 1 and next(queries) == nil and next(current) == nil)
    else
        assert(iterator_calls == 3 and current[2] == second)
        assert(queries[2] == 200)
        if mode == "stable" then
            assert(current[1] == first and queries[1] == 200 and queries[-1] == nil)
        else
            assert(current[1] ~= first and current[1].id == -1)
            assert(first.id == 1 and queries[1] == 1 and queries[-1] == 199)
        end
    end
    print(mode, iterator_calls, queries[1], queries[2], queries[-1])
end
run("empty")
run("stable")
run("update-once")
run("repeat-update")
pairs = saved_pairs
