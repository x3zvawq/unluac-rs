-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-contains [[local n = roll]] [[@debug=retained]]
-- Recover success/failure guard routes without evaluating the right side twice.
local function check(enabled, health, roll)
    if enabled then
        local n = roll
        if (health < 0.5 and n <= 90) or n <= 45 then
            print("bonus")
        end
    end
    print("tail")
end
for enabled = 0, 1 do
    for health = 1, 3, 2 do
        for roll = 44, 92, 2 do
            check(enabled == 1, health / 4, roll)
        end
    end
end

-- 多个外层 guard 共享完成点，但内层 if/else 的一臂仍由它独占；
-- 不应把该臂当成 single-pass tail，更不能改写其他内层分支的 continuation。
-- unluac: expect-ast-count [[repeat]] [[0]]
local function classify(platform, model, generation, emit)
    if model then
        if platform == "ios" then
            local number = generation
            if model and number then
                number = tonumber(number)
                if number then
                    local low = { iphone = 3, ipod = 4, ipad = 1 }
                    local high = { iphone = 5, ipod = 6, ipad = 3 }
                    if low[model] and high[model] then
                        if number <= low[model] then emit("low") end
                        if high[model] <= number then emit("high") end
                    else
                        emit("unknown")
                    end
                end
            end
        end
    else
        emit("missing")
    end
    emit("done")
end
local scenarios = {
    { "ios", false, "1", "missing,done" },
    { "other", "iphone", "1", "done" },
    { "ios", "iphone", false, "done" },
    { "ios", "iphone", "invalid", "done" },
    { "ios", "unknown", "1", "unknown,done" },
    { "ios", "iphone", "2", "low,done" },
    { "ios", "iphone", "4", "done" },
    { "ios", "iphone", "6", "high,done" },
    { "ios", "ipad", "1", "low,done" },
    { "ios", "ipad", "3", "high,done" },
}
for _, scenario in ipairs(scenarios) do
    local events = {}
    classify(scenario[1], scenario[2], scenario[3], function(event)
        events[#events + 1] = event
    end)
    local trace = table.concat(events, ",")
    assert(trace == scenario[4])
    print("nested closed arm", trace)
end

-- 同样的分区在外层循环内仍是普通 if/else，不能因全局 CFG 成环而拒绝。
local function update(self, ids, episodes, checker)
 local previous=nil
 for _, id in ipairs(ids) do
  if id==self.id then
   if previous then
    local pages=episodes[previous].pages
    local page=nil
    for i=#pages,0,-1 do
     if not page then
      page=pages[i]
      if page.skip then page=nil end
     end
    end
    if not page or checker:isOpen(page.levels[#page.levels]) then
     self.open=true
    end
   else
    self.open=true
   end
  end
  previous=id
 end
end

for scenario = 1, 5 do
    local self = { id = scenario == 1 and "first" or "second", open = false }
    local pages = { [0] = { skip = true }, { skip = scenario == 5, levels = { "last" } } }
    local calls = 0
    local checker = {}
    function checker:isOpen(level)
        assert(level == "last")
        calls = calls + 1
        return scenario == 2
    end
    local ids = { "first", "second" }
    if scenario == 4 then ids = {} end
    update(self, ids, { first = { pages = pages } }, checker)
    assert(self.open == (scenario == 1 or scenario == 2 or scenario == 5))
    assert(calls == ((scenario == 2 or scenario == 3) and 1 or 0))
    print("loop nested guard", scenario, self.open, calls)
end

-- elseif 共享最终 continuation，但每段复合条件仍有独立的两个出口。
do
    local function route(handled, key, editor, ended, ingame, emit, make_args)
        if not handled then
            if (key == "B" or key == "E") and (not editor or not editor.mode) then
                emit("back")
            elseif (key == "P" or key == "PAUSE") and not ended(make_args()) and ingame() then
                emit("pause")
            elseif key == "R" and ingame() then
                emit("replay")
            end
        end
        emit("done")
    end
    local function check_route(handled, key, editor, ended_value, mode, expected, expected_ended, expected_mode)
        local trace, ended_calls, mode_calls, argument_calls = "", 0, 0, 0
        route(handled, key, editor,
            function(...)
                assert(select("#", ...) == 2)
                local first, second = ...
                assert(first == nil and second == "marker")
                ended_calls = ended_calls + 1
                return ended_value
            end,
            function() mode_calls = mode_calls + 1; return mode end,
            function(event) trace = trace .. event .. "," end,
            function() argument_calls = argument_calls + 1; return nil, "marker" end)
        assert(trace == expected and ended_calls == expected_ended and mode_calls == expected_mode)
        assert(argument_calls == expected_ended)
        print("elseif condition boundaries", key, trace, ended_calls, mode_calls)
    end
    check_route(true, "P", nil, false, true, "done,", 0, 0)
    check_route(false, "B", nil, false, true, "back,done,", 0, 0)
    check_route(false, "E", false, false, true, "back,done,", 0, 0)
    check_route(false, "B", { mode = false }, false, true, "back,done,", 0, 0)
    check_route(false, "E", { mode = true }, false, true, "done,", 0, 0)
    check_route(false, "P", nil, false, true, "pause,done,", 1, 1)
    check_route(false, "PAUSE", nil, true, true, "done,", 1, 0)
    check_route(false, "P", nil, false, false, "done,", 1, 1)
    check_route(false, "R", nil, false, true, "replay,done,", 0, 1)
    check_route(false, "R", nil, false, false, "done,", 0, 1)
    check_route(false, "other", nil, false, true, "done,", 0, 0)
end

-- 内层短路的失败出口由外层 guard 共享；正常路径不能 goto 越过 return 臂。
do
    local function check_powerup(self, key)
        if self:used(key) and key ~= "a" and key ~= "b" and key ~= "c" and key ~= "d" then
            if key ~= "scope" then
                return false
            else
                local boosted = self:boosted(key)
                local count = self:count(key)
                if (boosted and count >= 2) or (not boosted and count >= 1) then
                    return false
                end
            end
        end
        self:finish(self.items[key])
        return true
    end
    for used = 0, 1 do
        for boosted = 0, 1 do
            for count = 0, 2 do
                for _, key in ipairs({ "a", "b", "c", "d", "scope", "other" }) do
                    local trace = ""
                    local self = { items = {} }
                    self.items[key] = key
                    function self:used(actual)
                        assert(actual == key)
                        trace = trace .. "u"
                        return used == 1
                    end
                    function self:boosted(actual)
                        assert(actual == key)
                        trace = trace .. "b"
                        return boosted == 1
                    end
                    function self:count(actual)
                        assert(actual == key)
                        trace = trace .. "c"
                        return count
                    end
                    function self:finish(actual)
                        assert(actual == key)
                        trace = trace .. "f"
                    end
                    local limited = used == 1 and key ~= "a" and key ~= "b" and key ~= "c" and key ~= "d"
                    local accepted = not limited or (key == "scope" and count < (boosted == 1 and 2 or 1))
                    assert(check_powerup(self, key) == accepted)
                    local expected = "u" .. (limited and key == "scope" and "bc" or "") .. (accepted and "f" or "")
                    assert(trace == expected)
                    print("shared return continuation", used, boosted, count, key, trace)
                end
            end
        end
    end
end
-- unluac: expect-contains [[if boosted and count >= 2 or not boosted and count >= 1 then]] [[@debug=retained]]

-- 循环体内共享判断节点不能被多前驱过滤截断；前置调用必须仍执行两次。
do
    local function check_dates(old, new, expired, show, mark)
        for iteration = 1, 2 do
            if old and new then
                mark("old", old)
                mark("new", new)
                if old.year < new.year
                    or old.year == new.year and old.month < new.month
                    or old.year == new.year and old.month == new.month and old.day < new.day then
                    if expired(old) then show(old) end
                else
                    if expired(new) then show(new) end
                end
            end
        end
        return 1
    end
    for dimension = 1, 3 do
        for direction = -1, 1 do
            for active = 0, 1 do
                local old = { year = 2020, month = 6, day = 15 }
                local new = { year = 2020, month = 6, day = 15 }
                if dimension == 1 then new.year = new.year + direction
                elseif dimension == 2 then new.month = new.month + direction
                else new.day = new.day + direction end
                local expected = new
                if direction > 0 then expected = old end
                local trace = ""
                local function expired(value)
                    assert(value == expected)
                    trace = trace .. "e"
                    return active == 1
                end
                local function show(value) assert(value == expected); trace = trace .. "s" end
                local function mark(which, value)
                    assert(which == "old" and value == old or which == "new" and value == new)
                    trace = trace .. which
                end
                assert(check_dates(old, new, expired, show, mark) == 1)
                local once = "oldnewe"
                if active == 1 then once = once .. "s" end
                assert(trace == once .. once)
                print("loop shared decision", dimension, direction, active, trace)
            end
        end
    end
end
-- unluac: expect-contains [[old.year < new.year]] [[@debug=retained]]

-- 值合流完成后仍有独立的循环 guard；取值 owner 不能吞掉后继条件。
-- unluac: expect-contains [[if levels[index].feathers_required and levels[index].feathers_required > 0 then]] [[@debug=retained]]
-- unluac: expect-not-contains [[or requires_powerups]] [[@debug=retained]]
do
    local function build(self, episode, frame, levels)
        for index = 1, #levels do
            local page = episode.pages[1]
            local requires_powerups = false
            if levels[index].feathers_required and levels[index].feathers_required > 0 then
                requires_powerups = true
            end
            if g_powerups_enabled or not requires_powerups then
                local button = g_ls_layout_mapping[page.layout].createBonusLevelButton(levels[index])
                frame:addChild(button)
            end
        end
        self:addChild(frame)
    end
    local saved_enabled, saved_layouts = g_powerups_enabled, g_ls_layout_mapping
    local levels = {
        { id = "n" }, { id = "f", feathers_required = false },
        { id = "z", feathers_required = 0 }, { id = "p", feathers_required = 1 },
    }
    for enabled = 0, 1 do
        g_powerups_enabled = enabled == 1
        local created, added, finished = "", "", 0
        g_ls_layout_mapping = { sample = {
            createBonusLevelButton = function(level)
                created = created .. level.id
                return level.id
            end,
        } }
        local frame = {}
        function frame:addChild(button) added = added .. button end
        local owner = {}
        function owner:addChild(child) assert(child == frame); finished = finished + 1 end
        build(owner, { pages = { { layout = "sample" } } }, frame, levels)
        local expected = enabled == 1 and "nfzp" or "nfz"
        assert(created == expected and added == expected and finished == 1)
        print("value merge before loop guard", enabled, created, added, finished)
    end
    g_powerups_enabled, g_ls_layout_mapping = saved_enabled, saved_layouts
end

-- 取值区域切断前一分支的条件图，但两侧仍能汇入后继的复合 guard。
-- 多入口弱连通分量必须按各自出口分段，不能整组放弃并留下 goto。
local function check_shared_guard_after_value_region()
    local function route(outer, option, flags, emit)
        if outer then
            local inner = option or 0
            if inner > 0 then emit("prepare;") end
        end
        if not flags.a and not flags.b and (flags.c and flags.d or flags.e or flags.f and flags.g) then
            emit("exit;")
            return
        end
        if (not flags.release or flags.cheats) and flags.pressed then emit("increase;") end
        emit("finish;")
    end
    local checks = 0
    for outer = 0, 1 do
        for option = 0, 2 do
            for mask = 0, 127 do
                local bits, flags = mask, {}
                for _, key in ipairs({"a", "b", "c", "d", "e", "f", "g"}) do
                    flags[key] = bits % 2 == 1
                    bits = math.floor(bits / 2)
                end
                for tail = 0, 3 do
                    flags.release = tail % 2 == 0
                    flags.cheats = tail == 2
                    flags.pressed = tail ~= 3
                    local trace = ""
                    local input = false
                    if option > 0 then input = option - 1 end
                    route(outer == 1, input, flags,
                        function(event) trace = trace .. event end)
                    local expected = ""
                    if outer == 1 and option == 2 then expected = "prepare;" end
                    local exit = false
                    if not flags.a and not flags.b then
                        if flags.c and flags.d then exit = true
                        elseif flags.e then exit = true
                        elseif flags.f and flags.g then exit = true end
                    end
                    if exit then
                        expected = expected .. "exit;"
                    else
                        if flags.pressed and (flags.cheats or not flags.release) then
                            expected = expected .. "increase;"
                        end
                        expected = expected .. "finish;"
                    end
                    assert(trace == expected)
                    checks = checks + 1
                end
            end
        end
    end
    print("shared guard after value region", checks)
end
check_shared_guard_after_value_region()
