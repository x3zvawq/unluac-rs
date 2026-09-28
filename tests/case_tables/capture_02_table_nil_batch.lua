-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=0]]
-- An initializer may contain nil holes and be captured after its SETLIST.
VALUES = { first = 7, third = 9 }
local t = { VALUES.first, VALUES.missing, VALUES.third }
local function read(i) return t[i] end
assert(read(1) == 7 and read(2) == nil and read(3) == 9)
assert(#t == 3)
print("captured-nil-batch", read(1), read(2), read(3), #t)

-- SELF 的 receiver COPY 已退休时仍从原定义恢复方法；后面的参数复用不得
-- 反向占有此前的 SETLIST。回调捕获的两个对象必须与表内对象保持同一身份。
-- unluac: expect-ast-count [[table-list-field]] [[14]]
-- unluac: expect-ast-count [[method-call]] [[10]]
local events, made = {}, {}
Factory = {}
function Factory:new()
    local object = { callbacks = {} }
    made[#made + 1] = object
    function object:load(name)
        self.name = name
        events[#events + 1] = "load:" .. name
    end
    function object:play(name)
        events[#events + 1] = "play:" .. self.name .. ":" .. name
    end
    function object:place(x, y)
        assert(x == 1 and y == 2.35)
        events[#events + 1] = "place:" .. self.name
    end
    function object:dispose()
        self.disposed = true
        events[#events + 1] = "dispose:" .. self.name
    end
    return object, "extra"
end
Store = {}
Cues = { done = "sound" }
function sound(cue)
    assert(cue == "sound")
    events[#events + 1] = cue
end
local function build_captured(point)
 local first = Factory:new()
 first:load("one")
 first:play("out")
 first:place(point.x, point.y + 0.35)
 first.callbacks.done = function() first:dispose() end
 local second = Factory:new()
 second:load("two")
 second:play("out")
 second:place(point.x, point.y + 0.35)
 second.callbacks.done = function() second:dispose(); Store[point] = nil end
 Store[point] = {first, second}
 sound(Cues.done)
end
local point = { x = 1, y = 2 }
build_captured(point)
local pair = Store[point]
assert(pair[1] == made[1] and pair[2] == made[2] and pair[3] == nil)
pair[1].callbacks.done()
assert(pair[1].disposed and not pair[2].disposed and Store[point] == pair)
pair[2].callbacks.done()
assert(pair[2].disposed and Store[point] == nil)
assert(table.concat(events, ",") == "load:one,play:one:out,place:one,load:two,play:two:out,place:two,sound,dispose:one,dispose:two")
print("captured constructor frames", table.concat(events, ","))

-- 原批次声明不能被两个合流结果拆散；构造器包含固定首项和开放尾项。
do
    local api = {}
    local owner = { transition = {} }
    local ready = true
    local trace = ""
    local function mark(value) trace = trace .. value end
    function api.block() mark("b"); return "block", "extra" end
    function api.whilst(predicate, block, extra)
        assert(predicate == "predicate" and block == "block" and extra == "extra")
        mark("w")
        return "wait", "discarded"
    end
    function api.action(callback) mark("a"); return callback, nil, "end" end
    function api.sequence(values)
        assert(values[1] == "wait" and values[3] == nil and values[4] == "end" and values[5] == nil)
        values[2]()
        mark("s")
        return values
    end
    owner.transition.is_animating = "predicate"
    function owner.transition.transition(record)
        assert(record.animation == record.content.expected)
        mark("t")
    end
    local animation = {}
    function animation.wobble(content, duration, count, offset)
        assert(duration == 0.25 and count == 4 and offset.x == 4 and offset.y == 0)
        mark("d")
        return content
    end
    local game = { width = 100 }
    local function animate(popup, create)
        if popup then
            local content, anim
            if popup.draw and popup.content then content = popup.content else content = popup end
            if create then
                assert(type(create) == "function")
                anim = create(content)
            else
                anim = animation.wobble(content, 0.25, 4, { x = game.width * 0.04, y = 0 })
            end
            owner.transition.transition({ content = popup, animation = anim })
            ready = true
            return api.sequence({
                api.whilst(owner.transition.is_animating, api.block()),
                api.action(function() if popup.entry then popup.entry() end end),
            })
        end
        ready = false
    end
    assert(animate(false, false) == nil and ready == false and trace == "")
    for scenario = 1, 3 do
        trace = ""
        local popup = { draw = scenario > 1, content = {} }
        popup.expected = popup
        if popup.draw then popup.expected = popup.content end
        function popup.entry() mark("e") end
        local create = false
        if scenario == 3 then create = function(content) mark("c"); return content end end
        local values = animate(popup, create)
        assert(ready and values[1] == "wait")
        assert(trace == (scenario == 3 and "ctbwaes" or "dtbwaes"))
        print("split nil constructor", scenario, trace, values[3], values[4])
    end
end

-- 固定字段的 NEWTABLE RHS 与后续 CALL 复用原槽；不能留下占槽的中转声明。
do
    local trace = ""
    local api = {}
    function api.make() trace = trace .. "m"; return 7 end
    function api.start() trace = trace .. "b"; return "first", "extra" end
    function api.action(callback) trace = trace .. "a"; return callback, nil, "end" end
    function api.sequence(values)
        assert(values[1] == "first" and values[3] == nil and values[4] == "end" and values[5] == nil)
        trace = trace .. "s"
        return values
    end
    local function initialize(self)
        self.queue = {}
        self.value = api.make()
        local mode = self.tint.mode or "plain"
        self.world[self.key].color = {R=self.tint.R, G=self.tint.G, B=self.tint.B, A=self.tint.A or 255, mode=mode}
        local first = api.start()
        self.state = api.sequence({ first, api.action(function() return self.queue end) })
    end
    local object = {key="target", world={target={}}, tint={R=11,G=23,B=47}}
    initialize(object)
    local color = object.world.target.color
    assert(color.R == 11 and color.G == 23 and color.B == 47 and color.A == 255 and color.mode == "plain")
    assert(object.value == 7 and object.state[2]() == object.queue and trace == "mbas")
    print("indexed allocation prefix", object.value, trace, object.state[4])
end
-- unluac: expect-contains [[self.queue = {}]] [[@debug=retained]]
-- unluac: expect-contains [[.color = {]]

-- CALL 的整包结果逆序写回已有 local 和低槽字段，后续 nil 声明复用结果区。
do
    local trace, blocks = "", {}
    local api = {}
    function api.block()
        local value = {}
        blocks[#blocks + 1] = value
        trace = trace .. "b"
        return value
    end
    function api.interruptible(block, callback)
        trace = trace .. "i"
        return block, callback
    end
    function api.action(callback) trace = trace .. "a"; return callback, nil, "tail" end
    function api.cycle(values)
        assert(values[2] == blocks[2] and values[3] == nil)
        trace = trace .. "c"
        return values
    end
    function api.whilst(predicate, cycle)
        assert(predicate() == true)
        trace = trace .. "w"
        return cycle
    end
    function api.sequence(values) trace = trace .. "s"; return values end
    local function initialize(self)
        self.queue = {}
        local done = true
        local ready
        local first, on_ready = api.interruptible(api.block(), function() done = true end)
        self.on_ready = on_ready
        ready = first
        local closing
        local second, on_close = api.interruptible(api.block(), function() done = false; return self.queue end)
        self.on_close = on_close
        closing = second
        self.state = api.sequence({
            ready,
            api.whilst(function() return done end, api.cycle({
                api.action(function() return self.queue end), closing,
            })),
            api.action(function() return done end),
        })
    end
    local object = {}
    initialize(object)
    local state = object.state
    assert(trace == "bibiacwas" and state[1] == blocks[1] and state[2][2] == blocks[2])
    assert(state[2][1]() == object.queue and state[3]() == true)
    assert(state[4] == nil and state[5] == "tail" and state[6] == nil)
    assert(object.on_close() == object.queue and state[3]() == false)
    object.on_ready()
    assert(state[3]() == true)
    print("mixed result writebacks", trace, state[5])
end
