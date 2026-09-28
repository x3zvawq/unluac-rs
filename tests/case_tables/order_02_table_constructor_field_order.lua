-- regress_212_table_constructor_field_order#1: pending integer fields keep binding snapshots
-- regress_212_table_constructor_field_order#2: pending integer fields keep metamethod order
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local value = 20

local function mutate()
    value = 30
    return 10
end

local binding_result = {}
binding_result[2] = value
binding_result[1] = mutate()
assert(binding_result[1] == 10 and binding_result[2] == 20 and value == 30)
print("regress_212_table_constructor_field_order#1", binding_result[1], binding_result[2], value)

local hits = 0
local operand = setmetatable({}, {
    __add = function()
        hits = hits + 1
        return hits
    end,
})

local function mark()
    hits = hits + 10
    return hits
end

local metamethod_result = {}
metamethod_result[2] = operand + 0
metamethod_result[1] = mark()
assert(metamethod_result[1] == 11 and metamethod_result[2] == 1 and hits == 11)
print("regress_212_table_constructor_field_order#2", metamethod_result[1], metamethod_result[2], hits)

-- 嵌套字段允许数值常量处于任一侧；共享帧须保留原运算方向和元方法顺序。
-- unluac: expect-ast-count [[table-list-field]] [[44]]
local function build_intervals(duration)
    local first = Tween.Ease:new({ interval = Tween.Scale:new({ duration = 0.5 * duration }) })
    local second = Tween.Ease:new({ interval = Tween.Scale:new({ duration = duration * 0.5 }) })
    local wait = Tween.Wait:new({ duration = 10 })
    return Tween.Queue:new({ tag = "queue", first, second, first, second, wait })
end

local function check_intervals()
    local saved_tween = Tween
    local trace, lookups = "", ""
    local function class(name)
        return setmetatable({}, { __index = function(_, key)
            assert(key == "new")
            -- VM 对方法查找与参数的先后约定不同；记录时点，由运行比较验证。
            lookups = lookups .. name .. ":" .. trace .. "|"
            return function(self, value)
                assert(self == Tween[name])
                trace = trace .. name .. ";"
                return value
            end
        end })
    end
    Tween = { Ease = class("Ease"), Scale = class("Scale"), Wait = class("Wait"), Queue = class("Queue") }
    local duration
    duration = setmetatable({}, { __mul = function(left, right)
        if left == 0.5 then
            assert(right == duration)
            trace = trace .. "left;"
            return 3
        end
        assert(left == duration and right == 0.5)
        trace = trace .. "right;"
        return 7
    end })
    local queue = build_intervals(duration)
    assert(queue.tag == "queue" and queue[1] == queue[3] and queue[2] == queue[4])
    assert(queue[1].interval.duration == 3 and queue[2].interval.duration == 7)
    assert(queue[5].duration == 10 and queue[6] == nil)
    assert(trace == "left;Scale;Ease;right;Scale;Ease;Wait;Queue;")
    print("nested arithmetic fields", trace, lookups)
    Tween = saved_tween
end
check_intervals()

-- 外层匿名绑定接收分支 CALL 的低槽写回，后续 SELF 副本仍在原调用处准备。
local function animate_branch(self, button)
    local image = button:getChild("image")
    local counter = button:getChild("counter")
    if image then
        image:setVisible(true)
        counter:setVisible(false)
    else
        image = ui.Image:new({ name = "image" })
        image:setImage("icon")
        button:addChild(image)
        image:setVisible(true)
        counter:setVisible(false)
        local scale = 1.1
        local duration = 500
        local first = tweens.EaseIn:new({ interval = tweens.Scale:new({ target = image, x = scale, y = scale, duration = 0.5 * duration }) })
        local second = tweens.EaseOut:new({ interval = tweens.Scale:new({ target = image, x = 1, y = 1, duration = 0.5 * duration }) })
        local wait = tweens.Wait:new({ duration = 500 })
        local queue = tweens.Queue:new({ tag = self, first, second, first, second, wait })
        local loop = tweens.Loop:new({ interval = queue })
        self.scheduler:addTween(loop)
        self:layout()
    end
end


local function check_branch_writeback()
    local old_ui, old_tweens = ui, tweens
    local trace = ""
    local image = {
        setImage = function(_, value) assert(value == "icon"); trace = trace .. "image;" end,
        setVisible = function(_, value) assert(value); trace = trace .. "visible;" end,
    }
    local counter = { setVisible = function(_, value) assert(not value); trace = trace .. "counter;" end }
    local current
    local button = {
        getChild = function(_, name) if name == "image" then return current else return counter end end,
        addChild = function(_, value) assert(value == image); trace = trace .. "child;" end,
    }
    ui = { Image = { new = function(_, spec) assert(spec.name == "image"); return image end } }
    local function constructor(name)
        return { new = function(_, spec) trace = trace .. name .. ";"; return spec end }
    end
    tweens = {
        EaseIn = constructor("in"), EaseOut = constructor("out"), Scale = constructor("scale"),
        Wait = constructor("wait"), Queue = constructor("queue"), Loop = constructor("loop"),
    }
    local result
    local owner = {
        scheduler = { addTween = function(_, value) result = value; trace = trace .. "add;" end },
        layout = function() trace = trace .. "layout;" end,
    }
    animate_branch(owner, button)
    local queue = result.interval
    assert(queue.tag == owner and queue[1] == queue[3] and queue[2] == queue[4] and queue[6] == nil)
    assert(queue[1].interval.target == image and queue[1].interval.x == 1.1)
    assert(queue[1].interval.duration == 250 and queue[2].interval.duration == 250)
    assert(queue[5].duration == 500)
    assert(trace == "image;child;visible;counter;scale;in;scale;out;wait;queue;loop;add;layout;")
    print("branch writeback", trace)
    current, trace = image, ""
    animate_branch(owner, button)
    assert(trace == "visible;counter;")
    print("branch existing", trace)
    ui, tweens = old_ui, old_tweens
end
check_branch_writeback()

-- 两侧字段读取和算术元方法必须按元素顺序完成，整个构造器之后才写回目标。
-- unluac: expect-contains [[.moveV = {]]
-- unluac: expect-contains [[.delta = {]]
local function build_vectors(self)
    self.moveV = { self.character.x - self.button.x, self.character.y - self.button.y }
    self.delta = { x = self.character.x - self.button.x, y = self.character.y - self.button.y }
end

local function check_vector_order()
    local trace, operations = "", 0
    local values = {}
    local function component(side, axis)
        return setmetatable({}, { __sub = function(left, right)
            assert(left == values[side .. axis] and right == values["right" .. axis])
            operations = operations + 1
            trace = trace .. "sub:" .. axis .. ";"
            return 100 + operations
        end })
    end
    values.leftx, values.lefty = component("left", "x"), component("left", "y")
    values.rightx, values.righty = {}, {}
    local function coordinates(side)
        return setmetatable({}, { __index = function(_, axis)
            trace = trace .. side .. ":" .. axis .. ";"
            return values[side .. axis]
        end })
    end
    local character, button = coordinates("left"), coordinates("right")
    local owner = setmetatable({}, {
        __index = function(_, key)
            trace = trace .. key .. ";"
            if key == "character" then return character end
            assert(key == "button")
            return button
        end,
        __newindex = function(self, key, value)
            assert(operations == (key == "moveV" and 2 or 4))
            trace = trace .. "store:" .. key .. ";"
            rawset(self, key, value)
        end,
    })
    build_vectors(owner)
    assert(owner.moveV[1] == 101 and owner.moveV[2] == 102 and owner.moveV[3] == nil)
    assert(owner.delta.x == 103 and owner.delta.y == 104)
    local pair = "character;left:x;button;right:x;sub:x;character;left:y;button;right:y;sub:y;"
    assert(trace == pair .. "store:moveV;" .. pair .. "store:delta;")
    print("constructor arithmetic", trace)
end
check_vector_order()

-- 一元参数既可能读取 CALL 结果，也可能读取字段；不能让前一种候选遮住后一种。
-- unluac: expect-contains [[.y, -]]
-- unluac: expect-contains [[x = -]]
local function split_vectors(obj)
    local function create(name, direction) return obj:add(name, direction) end
    local x, y = normalize(obj.y, -obj.x)
    local a = create("a", { x = -x, y = -y })
    local b = create("b", { x = x, y = y })
    local c = create("c", { x = 0, y = 0 })
    inherit(obj.name, { a, b, c })
    other = { a, b }
    return c
end

local function check_unary_preparation()
    local old_normalize, old_inherit, old_other = normalize, inherit, other
    local trace = ""
    local function vector(label, result)
        return setmetatable({}, { __unm = function()
            trace = trace .. "neg:" .. label .. ";"
            return result
        end })
    end
    local vx, vy, input = vector("x", -3), vector("y", -4), vector("input", -2)
    normalize = function(y, negative_x)
        assert(y == 7 and negative_x == -2)
        trace = trace .. "normalize;"
        return vx, vy
    end
    local created = {}
    local obj = setmetatable({}, { __index = function(_, key)
        trace = trace .. "get:" .. key .. ";"
        if key == "y" then return 7 end
        if key == "x" then return input end
        if key == "name" then return "vectors" end
        assert(key == "add")
        return function(self, name, direction)
            assert(self ~= nil)
            trace = trace .. "add:" .. name .. ";"
            created[name] = direction
            return direction
        end
    end })
    inherit = function(name, values)
        assert(name == "vectors" and values[1] == created.a and values[2] == created.b)
        assert(values[3] == created.c and values[4] == nil)
        trace = trace .. "inherit;"
    end
    assert(split_vectors(obj) == created.c)
    assert(other[1] == created.a and other[2] == created.b and other[3] == nil)
    assert(created.a.x == -3 and created.a.y == -4)
    assert(created.b.x == vx and created.b.y == vy and created.c.x == 0 and created.c.y == 0)
    assert(trace == "get:y;get:x;neg:input;normalize;neg:x;neg:y;get:add;add:a;get:add;add:b;get:add;add:c;get:name;inherit;")
    print("unary constructor preparation", trace)
    normalize, inherit, other = old_normalize, old_inherit, old_other
end
check_unary_preparation()

-- 中间 CALL 后的高槽数组元素仍属于同一构造器；记录字段不应截断外层方法帧。
-- unluac: expect-contains [[tasks = {]]
-- unluac: expect-contains [[Load.login("selection")]]
local function build_loading_view(self)
    self.loading = true
    local view = menu.LoadingView:new({
        name = "login", loadingView = "Loading", progressText = Localization:getValue("title"),
        tasks = { Load.check, Load.login("selection"), Load.server },
    })
    view.completionCallback = function() self:finish(view) end
    notifications:addChild(view)
end

local function check_nested_call_order()
    local old_menu, old_localization, old_load, old_notifications = menu, Localization, Load, notifications
    local trace, result = "", nil
    local check, login, server = {}, {}, {}
    Load = setmetatable({}, { __index = function(_, key)
        trace = trace .. "load:" .. key .. ";"
        if key == "check" then return check end
        if key == "server" then return server end
        assert(key == "login")
        return function(selection)
            assert(selection == "selection")
            trace = trace .. "login;"
            return login, "discarded"
        end
    end })
    Localization = { getValue = function(_, key)
        assert(key == "title"); trace = trace .. "title;"; return "progress"
    end }
    menu = { LoadingView = { new = function(_, spec)
        assert(spec.name == "login" and spec.loadingView == "Loading" and spec.progressText == "progress")
        assert(spec.tasks[1] == check and spec.tasks[2] == login and spec.tasks[3] == server)
        assert(spec.tasks[4] == nil)
        trace = trace .. "view;"
        return spec
    end } }
    notifications = { addChild = function(_, view)
        trace = trace .. "add;"; result = view
    end }
    local owner = { finish = function(self, view)
        assert(self.loading and view == result); trace = trace .. "finish;"
    end }
    build_loading_view(owner)
    assert(owner.loading and result ~= nil)
    result.completionCallback()
    assert(trace == "title;load:check;load:login;login;load:server;view;add;finish;")
    print("nested constructor call", trace)
    menu, Localization, Load, notifications = old_menu, old_localization, old_load, old_notifications
end
check_nested_call_order()

-- 原对象先承接常量字段写，再作为开放数组调用的 receiver。
-- unluac: expect-contains [[:setImage({]]
local function build_button_images(parent)
    local badge = game.shop:getChild("badge")
    if badge then badge:update() end
    local button = ui.Button:new()
    button.name = "sound"
    button:setImage({ game.image("on", game.settings:dark()), game.image("off", game.settings:dark()) })
    parent:addChild(button)
end

local function check_open_images(has_badge)
    local old_ui, old_game = ui, game
    local trace, images, result = "", nil, nil
    local dark = 0
    game = {
        shop = { getChild = function(_, name)
            assert(name == "badge"); trace = trace .. "badge;"
            if has_badge then
                return { update = function() trace = trace .. "update;" end }
            end
        end },
        settings = { dark = function()
            dark = dark + 1; trace = trace .. "dark;"; return dark, nil, "tail"
        end },
        image = function(name, state, hole, tail)
            assert(state == (name == "on" and 1 or 2) and hole == nil and tail == "tail")
            trace = trace .. name .. ";"
            return name, nil, "extra"
        end,
    }
    ui = { Button = { new = function()
        trace = trace .. "new;"
        return { setImage = function(self, values)
            assert(self.name == "sound")
            images, result = values, self
            trace = trace .. "images;"
        end }
    end } }
    local parent = { addChild = function(_, child)
        assert(child == result); trace = trace .. "add;"
    end }
    build_button_images(parent)
    assert(images[1] == "on" and images[2] == "off" and images[3] == nil and images[4] == "extra")
    assert(images[5] == nil and dark == 2)
    assert(trace == "badge;" .. (has_badge and "update;" or "") .. "new;dark;on;dark;off;images;add;")
    print("constructor open images", trace)
    ui, game = old_ui, old_game
end
check_open_images(false)
check_open_images(true)

-- 条件单次读取的对象仍占据分支 CALL 下方的槽，后继构造器也沿用这个声明前缀。
-- unluac: expect-not-contains [[:getChild("old") ~= nil]]
local function build_after_branch(self)
    local unused = self:getChild("old")
    if unused ~= nil then self:remove(self:getChild("old")) end
    local a = menu.View:new({ name = "a", visible = self:visible() })
    self:add(a)
    local b = menu.View:new({ name = "b" })
    self:queue({ a, b })
end

local function check_branch_prefix(has_old)
    local old_menu = menu
    local trace, reads, result = "", 0, nil
    local weak = setmetatable({}, { __mode = "v" })
    menu = { View = { new = function(_, spec)
        trace = trace .. spec.name .. ";"; return spec
    end } }
    local owner = {
        getChild = function(_, name)
            assert(name == "old")
            reads = reads + 1; trace = trace .. "get;"
            if not has_old then return nil end
            local value = {}
            weak[reads] = value
            return value
        end,
        remove = function(_, value)
            assert(value == weak[2])
            local collect = rawget(_G, "collectgarbage")
            if collect then collect("collect") end
            assert(weak[1] ~= nil)
            trace = trace .. "remove;"
        end,
        visible = function() trace = trace .. "visible;"; return true end,
        add = function(_, value) result = value; trace = trace .. "add;" end,
        queue = function(_, values)
            assert(values[1] == result and result.visible and values[2].name == "b" and values[3] == nil)
            trace = trace .. "queue;"
        end,
    }
    build_after_branch(owner)
    assert(reads == (has_old and 2 or 1))
    assert(trace == (has_old and "get;get;remove;" or "get;") .. "visible;a;add;b;queue;")
    print("branch constructor prefix", has_old, trace)
    menu = old_menu
end
check_branch_prefix(true)
check_branch_prefix(false)

-- 另一 proto 的字段整理会让 temp-inline 在 Local 提升前再次执行。
-- 后续分支的前缀义务属于新 Def，不能阻止先前同槽 CALL 写入全局。
-- unluac: expect-contains [[constructor_logo = FrameLogo:new({]]
-- unluac: expect-contains [[FrameTween.Wait:new({]]
local function prepare_frame_context()
    return { sum = frame_value() + 2 }
end

local function build_reused_frame(self, flag)
    constructor_logo = FrameLogo:new({ name = "logo" })
    local wallet = self:getChild("wallet")
    if wallet ~= nil then self:remove(self:getChild("wallet")) end
    local queue = FrameTween.Queue:new({
        FrameTween.Wait:new({ duration = 500 }), flag,
    })
end

local function check_reused_frame(has_wallet)
    local old_logo, old_tween = FrameLogo, FrameTween
    local old_result, old_value = constructor_logo, frame_value
    local trace, result, reads = "", nil, 0
    frame_value = function() trace = trace .. "value;"; return 7 end
    assert(prepare_frame_context().sum == 9)
    FrameLogo = { new = function(_, spec)
        assert(spec.name == "logo"); trace = trace .. "logo;"; return spec
    end }
    FrameTween = {
        Wait = { new = function(_, spec)
            assert(spec.duration == 500); trace = trace .. "wait;"; return spec, "discarded"
        end },
        Queue = { new = function(_, spec)
            result = spec; trace = trace .. "queue;"; return spec
        end },
    }
    local owner = {
        getChild = function(_, name)
            assert(name == "wallet" and constructor_logo.name == "logo")
            reads = reads + 1; trace = trace .. "get;"
            if has_wallet then return { read = reads } end
        end,
        remove = function(_, wallet)
            assert(wallet.read == 2); trace = trace .. "remove;"
        end,
    }
    local flag = {}
    build_reused_frame(owner, flag)
    assert(result[1].duration == 500 and result[2] == flag and result[3] == nil)
    assert(reads == (has_wallet and 2 or 1))
    assert(trace == "value;logo;" .. (has_wallet and "get;get;remove;" or "get;") .. "wait;queue;")
    print("constructor reused frame", has_wallet, trace)
    FrameLogo, FrameTween = old_logo, old_tween
    constructor_logo, frame_value = old_result, old_value
end
check_reused_frame(true)
check_reused_frame(false)
-- CONCAT 的独立恢复不能截走字段准备；两次构造再进入后续数组帧。
-- unluac: expect-contains [[tag = "drop" ..]]
-- unluac: expect-contains [[tag = "end" ..]]
local function build_concat_frames(owner)
    local first = FrameTag:new({ tag = "drop" .. owner.level })
    local second = FrameTag:new({ tag = "end" .. owner.level })
    FrameCollect({ first, second })
end
local function check_concat_frames()
    local old_tag, old_collect = FrameTag, FrameCollect
    local trace, objects = "", {}
    local level = setmetatable({}, { __concat = function(prefix, value)
        assert(value ~= nil)
        trace = trace .. prefix .. ";"
        return prefix .. "7"
    end })
    FrameTag = { new = function(_, value)
        trace = trace .. "new;"
        objects[#objects + 1] = value
        return value, "discarded"
    end }
    FrameCollect = function(values)
        assert(values[1] == objects[1] and values[2] == objects[2] and values[3] == nil)
        assert(values[1].tag == "drop7" and values[2].tag == "end7")
        trace = trace .. "collect;"
    end
    build_concat_frames({ level = level })
    assert(trace == "drop;new;end;new;collect;")
    print("constructor concat frames", trace)
    FrameTag, FrameCollect = old_tag, old_collect
end
check_concat_frames()
-- 分支内外复用 receiver COPY 槽，低槽 CALL 结果仍有各自的声明身份。
-- unluac: expect-count [[:setImages({]] [[3]]
local function update_three_buttons(self)
    local sound = self:getChild("sound")
    sound:setImages({ FrameImages.image("on", FrameImages.settings:dark()), FrameImages.image("off", FrameImages.settings:dark()) })
    if FrameImages.supported() then
        local button = self:getChild("dolby")
        button:setImages({ FrameImages.image("on", FrameImages.settings:dark()), FrameImages.image("on", FrameImages.settings:dark()) })
    end
    local hints = self:getChild("hints")
    hints:setImages({ FrameImages.image("on", FrameImages.settings:dark()), FrameImages.image("off", FrameImages.settings:dark()) })
end
local function check_three_buttons(supported)
    local old_images = FrameImages
    local trace, count, dark = "", 0, 0
    FrameImages = {
        supported = function() trace = trace .. "supported;"; return supported end,
        settings = { dark = function() dark = dark + 1; return dark, "mode" end },
        image = function(name, state, mode)
            assert(state == dark and mode == "mode")
            trace = trace .. name .. ";"
            return name, nil, "tail"
        end,
    }
    local owner = { getChild = function(_, name)
        trace = trace .. name .. ";"
        local child = {}
        child.setImages = function(self, values)
            assert(self == child)
            assert(values[1] == "on" and values[2] == (name == "dolby" and "on" or "off"))
            assert(values[3] == nil and values[4] == "tail" and values[5] == nil)
            count = count + 1; trace = trace .. "images;"
        end
        return child
    end }
    update_three_buttons(owner)
    assert(count == (supported and 3 or 2) and dark == count * 2)
    assert(trace == "sound;on;off;images;supported;" ..
        (supported and "dolby;on;on;images;" or "") .. "hints;on;off;images;")
    print("constructor branch receivers", supported, trace)
    FrameImages = old_images
end
check_three_buttons(false)
check_three_buttons(true)

-- 条件与深层构造字段共享 CALL 结果；分支边界结束准备区，但不能丢掉跨域读取。
local function build_cross_region(self, id, points, done)
    local old_index = 1
    do
        local new_index = #self.scores + 1
        for index, score in ipairs(self.scores) do
            if score.points < points or score.id == id then
                new_index = index
                break
            end
        end
        local rank = 2
        local removed = table.remove(self.scores, old_index)
        print("rank " .. removed.rank .. " to " .. rank)
        local item = self:getItem(old_index)
        if item then
            local wait = FrameTween.Wait:new({time=300})
            local queue = FrameTween.Queue:new({
                FrameTween.Callback:new({callback=function() done("first") end}),
                FrameTween.Ease:new({rate=self.rate, interval=FrameTween.Move:new({target=item})})
            })
            local callback = FrameTween.Callback:new({callback=function()
                item = self:getItem(new_index)
                done("last", item.x, wait.time)
            end})
            self.scheduler:addTween(FrameTween.Queue:new({wait, queue, wait, callback}))
        end
    end
end

local function check_cross_region(has_item)
    local old_tweens = FrameTween
    local trace, result = "", nil
    local function factory(name)
        return {new=function(_, value)
            trace = trace .. name .. ";"
            return value
        end}
    end
    FrameTween = {
        Wait=factory("wait"), Queue=factory("queue"), Callback=factory("callback"),
        Ease=factory("ease"), Move=factory("move"),
    }
    local items = {{x=10}, {x=20}}
    local owner = {
        scores={{id=0, points=10, rank=4}, {id=7, points=1, rank=5}}, rate=2,
        getItem=function(_, index)
            trace = trace .. "get:" .. index .. ";"
            if has_item then return items[index] end
        end,
        _scheduler={addTween=function(_, value)
            result = value
            trace = trace .. "schedule;"
        end},
    }
    setmetatable(owner, {__index=function(receiver, key)
        assert(key == "scheduler")
        trace = trace .. "receiver;"
        return receiver._scheduler
    end})
    build_cross_region(owner, 7, 5, function(stage, x, wait)
        trace = trace .. stage .. ";"
        if stage == "last" then assert(x == 20 and wait == 300) end
    end)
    assert(#owner.scores == 1 and owner.scores[1].id == 7)
    if has_item then
        assert(#result == 4 and result[1] == result[3] and result[1].time == 300)
        assert(#result[2] == 2 and result[2][2].rate == 2)
        assert(result[2][2].interval.target == items[1])
        result[2][1].callback()
        result[4].callback()
        assert(trace == "get:1;wait;callback;move;ease;queue;callback;receiver;queue;schedule;first;get:2;last;")
    else
        assert(result == nil and trace == "get:1;")
    end
    print("cross-region constructor", has_item, trace)
    FrameTween = old_tweens
end
check_cross_region(false)
check_cross_region(true)

-- unluac: expect-contains [[interval = FrameTween.Move:new({]]
-- unluac: expect-contains [[:addTween(FrameTween.Queue:new({]]
