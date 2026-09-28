-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=luau]]
-- 列表准备和 iterator 结果必须共同恢复，循环携带的 sum 不应截断构造事务。
local function total(Activity)
    local sum = 0
    for _, v in ipairs({Activity.IDS.M_BOX_1.ID, Activity.IDS.M_BOX_2.ID}) do
        sum = sum + v
    end
    return sum
end

local trace = {}
local values = {3, 7}
local boxes = {}
for index = 1, 2 do
    boxes["M_BOX_" .. index] = setmetatable({}, {
        __index = function(_, key)
            trace[#trace + 1] = index .. ":" .. key
            return values[index]
        end,
    })
end
local activity = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = key
        return boxes
    end,
})
assert(total(activity) == 10)
assert(table.concat(trace, ",") == "IDS,1:ID,IDS,2:ID")
values[1], values[2] = -2, 11
assert(total(activity) == 9)
print("iterator frames", table.concat(trace, ","))

-- 连续迭代器共用声明，后继捕获的新值不能封锁旧 SETLIST 缓冲。
-- unluac: expect-contains [[Settings:check("a") and "A" or false]] [[@dialect=lua5.1]]
local function prepare(self)
for _, child in pairs(self.children) do child:setVisible(false) end
for name, bird in pairs(birds) do setVisible(name, false) end
local queue = self.queue
local count = 0
local position = objects.world.position
local groups={"one", "two", Settings:check("a") and "A" or false,
 Settings:check("b") and "B" or false, Settings:check("c") and "C" or false,
 "end1", "end2", "end3"}
local animations={}
for _, name in ipairs(groups) do
 if name then
  local a=Animation:new()
  a:loadFile("animations/"..name..".json")
  a:play("intro")
  a:setPaused(true)
  a:placeInWorld(position.x, position.y)
  count=count+1
  a.callbacks.END=function() count=count-1 end
  table.insert(animations,a)
 end
end
local camera=Animation:new()
camera:loadFile("camera")
camera:play("intro")
camera:setPaused(true)
camera:placeInWorld(position.x, position.y)
self:doDelayed(0,function()camera:setPaused(false) end)
DrawCalls.add("draw", -1, function() for _, item in ipairs(animations) do item:draw() end end)
return queue, count, animations, function() return count end
end


local function check_preparations()
    local saved = {birds=birds, setVisible=setVisible, objects=objects,
        Settings=Settings, Animation=Animation, DrawCalls=DrawCalls}
    local trace = ""
    local delayed, draw
    birds = {bird=true}
    setVisible = function(name, value) assert(name == "bird" and not value); trace=trace .. "bird;" end
    local child = {setVisible=function(_, value) assert(not value); trace=trace .. "child;" end}
    local owner = {children={child}, doDelayed=function(_, delay, callback) assert(delay==0); delayed=callback end}
    local queue = {}
    owner.queue = queue
    objects = {world={position={x=3,y=7}}}
    Settings = {check=function(_, key) trace=trace .. key .. ";"; return key~="b" end}
    local created = 0
    local last_created
    local draws = 0
    Animation = {new=function()
        created=created+1
        local item = {callbacks={}, loadFile=function(self, file) self.file=file end,
            play=function(_, name) assert(name=="intro") end,
            setPaused=function(self, value) self.paused=value end,
            placeInWorld=function(_, x,y) assert(x==3 and y==7) end,
            draw=function() draws=draws+1 end}
        last_created = item
        return item
    end}
    DrawCalls = {add=function(name, depth, callback) assert(name=="draw" and depth==-1); draw=callback end}
    local actual, count, animations, remaining = prepare(owner)
    assert(actual==queue and count==7 and #animations==7 and created==8)
    assert(trace=="child;bird;a;b;c;")
    assert(animations[3].file=="animations/A.json" and animations[4].file=="animations/C.json")
    for _, item in ipairs(animations) do assert(item.paused); item.callbacks.END() end
    assert(remaining()==0)
    draw(); delayed()
    assert(draws==7 and last_created.file=="camera" and not last_created.paused)
    assert(animations[1].paused)
    print("iterator reused frames", trace, count, remaining(), draws)
    birds, setVisible, objects = saved.birds, saved.setVisible, saved.objects
    Settings, Animation, DrawCalls = saved.Settings, saved.Animation, saved.DrawCalls
end
check_preparations()

-- 字段 scratch 随后被新 closure 捕获，原 GETTABLE/GETGLOBAL 仍属于初始化帧。
-- unluac: expect-contains [[accept({]]
local function field_frame(input)
    local result = accept({value=input.key, callback=globalCallback})
    local count = 0
    local later = {}
    publish(function() count=count+1; return later,count end)
    return result
end
local function check_field_frame()
    local old_accept, old_publish, old_callback = accept, publish, globalCallback
    local saved, trace
    trace = ""
    globalCallback = function() return "callback" end
    accept = function(value)
        assert(value.value==42 and value.callback==globalCallback)
        trace=trace .. "accept;"
        return value
    end
    publish = function(value) saved=value; trace=trace .. "publish;" end
    local value = field_frame(setmetatable({}, {__index=function(_, key)
        assert(key=="key"); trace=trace .. "read;"; return 42
    end}))
    local first, one = saved()
    local second, two = saved()
    assert(first==second and one==1 and two==2 and value.callback()=="callback")
    assert(trace=="read;accept;publish;")
    print("field future capture", trace, one, two)
    accept, publish, globalCallback = old_accept, old_publish, old_callback
end
check_field_frame()

-- 嵌套词法块的循环 carrier 仍认回原 seed；iterator 准备不应留下同槽交棒。
-- unluac: expect-contains [[RankFrames:make({]]
-- unluac: expect-contains [[RankFrames.accept({]]
local function rerank(self, score)
    local changed
    if self.scores then
        for k, v in ipairs(self.scores) do
            if v.id == score then
                if v.points ~= score then v.points = score; changed = k end
                break
            end
        end
    end
    if changed then
        local index = #self.scores + 1
        for k, v in ipairs(self.scores) do
            if v.points < score then index = k; break end
        end
        local rank
        if index ~= #self.scores + 1 then
            rank = self.scores[index].rank
        else
            rank = self.scores[#self.scores].rank + 1
        end
        local item = table.remove(self.scores, changed)
        item.rank = rank
        for k, v in ipairs(self.scores) do v.rank = v.rank + 1 end
        table.insert(self.scores, index, item)
        local frame = RankFrames:make({target = item, callback=function() return index, changed end})
        local function read_frame() return frame end
        RankFrames.accept({frame, index, read_frame})
    end
end

local function check_rerank()
    local old = RankFrames
    local received, calls = nil, 0
    RankFrames = {
        make = function(self, spec)
            assert(self == RankFrames)
            calls = calls + 1
            return spec, "discarded"
        end,
        accept = function(items)
            assert(items[4] == nil and items[3]() == items[1])
            local index, changed = items[1].callback()
            assert(index == items[2] and changed == 2)
            received = items
        end,
    }
    local first, moved, last = {id=1, points=9, rank=1},
        {id=5, points=1, rank=2}, {id=3, points=2, rank=3}
    local owner = {scores={first, moved, last}}
    rerank(owner, 5)
    assert(calls == 1 and received[1].target == moved and received[2] == 3)
    assert(owner.scores[1] == first and owner.scores[2] == last and owner.scores[3] == moved)
    assert(moved.points == 5 and moved.rank == 3 and first.rank == 2 and last.rank == 4)
    rerank(owner, 5)
    rerank(owner, 17)
    rerank({}, 5)
    assert(calls == 1)
    print("nested iterator carrier", calls, moved.rank, last.rank)
    RankFrames = old
end
check_rerank()

-- 同槽 nil owner 经多个独立分支更新，后续 SETLIST 不应被额外 phi 声明挤出原帧。
-- 动态全局表左值必须先于 key 求值，不能留下阻断整个后缀的快照 local。
-- unluac: expect-contains [[FrameInherit(definition.name, {]] [[@debug=retained]]
-- unluac: expect-contains [[FrameOthers = {]]
local function branch_frames(object, flag)
    local definition = FrameDefinition(object.name)
    if definition then
        local removed = nil
        if flag == "bomb" then removed = object end
        if flag == "cluster" then
            local function spawn(suffix, velocity)
                return FrameCreate(object.name .. suffix, velocity)
            end
            local dx, dy = FrameNormalize(object.yVel, -object.xVel)
            local a = spawn("a", {x=-dx, y=-dy})
            local b = spawn("b", {x=dx, y=dy})
            local c = spawn("c", {x=object.xVel, y=object.yVel})
            if FrameHats[object.name] then
                FrameHats[c] = FrameHats[object.name]
                FrameHats[object.name] = nil
            end
            FrameInherit(definition.name, {a, b, c})
            FrameOthers = {a, b}
            removed = object
        end
        if removed ~= nil then FrameRemove(removed) end
        return removed
    end
end

local function check_branch_frames()
    local old = {FrameDefinition, FrameNormalize, FrameCreate, FrameHats, FrameInherit, FrameOthers, FrameRemove}
    local events, received = "", nil
    FrameDefinition = function(name)
        events=events.."definition;"
        if name=="bird" then return {name=name} end
    end
    FrameNormalize = function(x,y) assert(x==4 and y==-3); events=events.."normalize;"; return 4,-3 end
    FrameCreate = function(name, velocity)
        events=events..name..";"
        return {name=name, velocity=velocity}, "discarded"
    end
    local hat = {}
    FrameHats = setmetatable({}, {
        __index=function(_,key) assert(key=="bird"); events=events.."hat-read;"; return hat end,
        __newindex=function(_,key,value)
            if key=="bird" then assert(value==nil); events=events.."hat-clear;"
            else assert(key.name=="birdc" and value==hat); events=events.."hat-copy;" end
        end,
    })
    FrameInherit = function(name, items)
        assert(name=="bird" and #items==3 and items[4]==nil)
        assert(items[1].name=="birda" and items[2].name=="birdb" and items[3].name=="birdc")
        assert(items[1].velocity.x==-4 and items[1].velocity.y==3)
        assert(items[2].velocity.x==4 and items[2].velocity.y==-3)
        assert(items[3].velocity.x==3 and items[3].velocity.y==4)
        received=items; events=events.."inherit;"
    end
    local object = {name="bird",xVel=3,yVel=4}
    FrameRemove = function(value) assert(value==object); events=events.."remove;" end
    assert(branch_frames(object,"cluster")==object)
    assert(FrameOthers[1]==received[1] and FrameOthers[2]==received[2] and FrameOthers[3]==nil)
    assert(events=="definition;normalize;birda;birdb;birdc;hat-read;hat-read;hat-copy;hat-clear;inherit;remove;")
    print("branch constructor frames",events)
    events=""
    assert(branch_frames(object,"bomb")==object)
    assert(events=="definition;remove;")
    events=""
    assert(branch_frames(object,"none")==nil and branch_frames({name="missing"},"cluster")==nil)
    assert(events=="definition;definition;")
    FrameDefinition, FrameNormalize, FrameCreate, FrameHats, FrameInherit, FrameOthers, FrameRemove =
        old[1],old[2],old[3],old[4],old[5],old[6],old[7]
end
check_branch_frames()

-- unluac: expect-contains [=[state = state_keys[state_key(7)]]=] [[@debug=retained]]
-- unluac: expect-contains [[a = { first() }]] [[@debug=retained]]
-- unluac: expect-contains [[b = { third(a) }]] [[@debug=retained]]
-- unluac: expect-contains [[a = { third(b) }]] [[@debug=retained]]
-- 跨轮值之间有未读槽：入口省略 LOADNIL，SETLIST 仍从完整声明区之上准备。
local state_keys, state_key_calls = {[7] = 2}, 0
local function state_key(value)
    state_key_calls = state_key_calls + 1
    return value
end
local function sparse_state_slots(state, first, second, third)
    local a, scratch, b
    while state do
        if state == 1 then
            a = { first() }
            scratch = second(7)
            state = state_keys[state_key(7)]
            b = { third(a) }
        else
            scratch = second(9)
            a = { third(b) }
            state = nil
        end
    end
    return a, b
end

local function check_sparse_state_slots()
    local events = ""
    local function first()
        events = events .. "first;"
        return 11, 12
    end
    local function second(value)
        events = events .. "second" .. value .. ";"
        return {value}, "discarded"
    end
    local function third(value)
        events = events .. "third;"
        return value, 19, 23
    end
    local a, b = sparse_state_slots(1, first, second, third)
    assert(a[1] == b and a[2] == 19 and a[3] == 23 and a[4] == nil)
    assert(b[1][1] == 11 and b[1][2] == 12 and b[1][3] == nil)
    assert(b[2] == 19 and b[3] == 23 and b[4] == nil)
    assert(events == "first;second7;third;second9;third;" and state_key_calls == 1)
    events = ""
    local empty_a, empty_b = sparse_state_slots(nil, first, second, third)
    assert(empty_a == nil and empty_b == nil and events == "")
    local partial_a, partial_b = sparse_state_slots(2, first, second, third)
    assert(partial_a[1] == nil and partial_a[2] == 19 and partial_a[3] == 23)
    assert(partial_b == nil and events == "second9;third;" and state_key_calls == 1)
    events = ""
    state_keys[7] = false
    local once_a, once_b = sparse_state_slots(1, first, second, third)
    assert(once_b[1] == once_a and once_a[1] == 11 and once_a[2] == 12)
    assert(events == "first;second7;third;" and state_key_calls == 2)
    state_keys[7] = 2
    print("sparse entry slots", a[2], b[1][1], events)
end
check_sparse_state_slots()

-- 低槽 GETTABLE 写回后才 COPY 到 callee；后续 SETLIST 复用相同调用准备区。
-- unluac: expect-contains [[target = registry.resolveLoopSlot]] [[@debug=retained]]
-- unluac: expect-contains [[packed = { consumer(result) }]] [[@debug=retained]]
do
    local calls = 0
    local registry = {resolveLoopSlot = function(a, b)
        calls = calls + 1
        return a + b
    end}
    local function low_lookup_carrier(state, consumer)
        local result, target, a, packed
        while state do
            if state == 1 then
                a, packed = 11, 19
                target = registry.resolveLoopSlot
                result = target(a, packed)
                target = 1
                packed = { consumer(result) }
                state = nil
            else
                state = 1
            end
        end
        return result, packed
    end
    local consumed = 0
    local function consume(value)
        consumed = consumed + 1
        return value, value + 1
    end
    local result, packed = low_lookup_carrier(2, consume)
    assert(result == 30 and packed[1] == 30 and packed[2] == 31 and packed[3] == nil)
    assert(calls == 1 and consumed == 1)
    local empty_result, empty_packed = low_lookup_carrier(nil, consume)
    assert(empty_result == nil and empty_packed == nil and calls == 1 and consumed == 1)
    print("lookup carried frame", result, packed[2], calls, consumed)
end

-- 已消费数组 COPY 的额外源码根须与字段一起退休；同一结果还参与后项 CONCAT。
-- unluac: expect-contains [[cache({ name, name .. "_cloud", "common", "common_cloud" })]] [[@debug=retained]]
do
    local calls = 0
    arrayProfileSource = {getDefaultProfile = function() return "a", "b", "name" end}
    arrayProfileSink = {cache = function(values)
        calls = calls + 1
        assert(#values == 4 and values[1] == "name" and values[2] == "name_cloud")
        assert(values[3] == "common" and values[4] == "common_cloud")
    end}
    arrayProfileEnabled = true
    local function load_profiles()
        if arrayProfileEnabled then
            local first, second, name = arrayProfileSource.getDefaultProfile()
            arrayProfileSink.cache({name, name .. "_cloud", "common", "common_cloud"})
        end
    end
    load_profiles()
    arrayProfileEnabled = false
    load_profiles()
    assert(calls == 1)
    print("array-profile-frame", calls)
end

-- 旧调用别名的词法段结束后，尾调用复用原槽，并原样消费含 nil 的 VARARG 包。
do
    local function process(consumer, ...)
        local names = {"ab", "cd"}
        do
            local join, measure = table.concat, string.len
            for index, name in ipairs(names) do
                local parts = {}
                for i = 1, measure(name) do parts[i] = name:sub(i, i) end
                names[index] = join(parts)
            end
        end
        return consumer(names, {...})
    end
    local first, last = process(function(names, args)
        assert(names[1] == "ab" and names[2] == "cd")
        assert(args[1] == 17 and args[2] == nil and args[3] == 29)
        return args[1], args[3]
    end, 17, nil, 29)
    assert(first == 17 and last == 29)
    print("return-vararg-frame", first, last)
end

-- 开放 SETLIST 的旧 callee 槽在兄弟分支内各自成为新声明，不能相互延长身份。
-- unluac: expect-contains [[:setEpochFrames({]]
do
    local saved_ui, saved_api = EpochUI, EpochAPI
    local events, made = "", 0
    EpochUI = {new=function()
        made = made + 1
        return {setEpochFrames=function(self, frames)
            self.frames = frames
            events = events .. "store;"
        end}
    end}
    EpochAPI = {
        settings={dark=function() events=events .. "dark;"; return true end},
        image=function(name, dark)
            assert(dark)
            events=events .. name .. ";"
            return name, name .. "-tail"
        end,
    }
    local function build(left, right)
        local first = EpochUI:new()
        first:setEpochFrames({EpochAPI.image("on", EpochAPI.settings:dark()),
            EpochAPI.image("off", EpochAPI.settings:dark())})
        if left then
            local second = EpochUI:new()
            second.name = "left"
            second:setEpochFrames(EpochAPI.image("left", EpochAPI.settings:dark()))
        end
        if right then
            local third = EpochUI:new()
            third.name = "right"
            third:setEpochFrames(EpochAPI.image("right", EpochAPI.settings:dark()))
        end
        return first
    end
    for mask = 0, 3 do
        local left, right = mask % 2 == 1, mask >= 2
        made, events = 0, ""
        local result = build(left, right)
        assert(made == 1 + (left and 1 or 0) + (right and 1 or 0))
        assert(#result.frames == 3 and result.frames[1] == "on"
            and result.frames[2] == "off" and result.frames[3] == "off-tail")
        assert(events == "dark;on;dark;off;store;"
            .. (left and "dark;left;store;" or "")
            .. (right and "dark;right;store;" or ""))
    end
    EpochUI, EpochAPI = saved_ui, saved_api
    print("sibling-frame-epochs", made, events)
end
