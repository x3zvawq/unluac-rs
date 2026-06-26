-- regress_37_shared_terminal_closure_tail#1: 带 closure 的共享 terminal tail 不能被复制进 if/else 双臂
-- unluac: expect-contains [[callback = function]]
-- unluac: expect-not-contains [[closure capture evidence is ambiguous]]
-- unluac: expect-not-contains [[unluac error]]

TweenSubsystem = {
    add = function(self, spec)
        spec.callback(3)
        if spec.doneCallback then
            spec.doneCallback()
        end
    end,
}

Manager = {
    isConnected = function()
        return false
    end,
}

local function getHighscore()
    return 42
end

local function make_obj(old_score, new_score)
    return {
        oldHighscore = old_score,
        scoreToPost = new_score,
    }
end

local function make_button()
    return {
        name = "button",
        w = 5,
    }
end

local function set_visible(button, value)
    button.visible = value
end

local function layout_position(button)
    return 10, 20
end

local function set_position(button, x, y)
    button.x = x
    button.y = y
end

local function make_score()
    return {
        name = "score",
    }
end

local function set_score(score, value)
    score.value = value
end

local function add_friend(obj, score, index)
    obj.friend = score.name .. index
end

local function add_new_score(obj, score)
    obj.added = score.name
end

local function show(obj)
    if Manager then
        if Manager.isConnected() then
        else
            local is_new = false
            local score = make_score()
            if obj.oldHighscore < obj.scoreToPost then
                set_score(score, obj.oldHighscore)
                is_new = true
            else
                set_score(score, getHighscore())
            end

            add_friend(obj, score, 0)
            local button = make_button()
            set_visible(button, true)
            local x, y = layout_position(button)
            local start = x + button.w
            TweenSubsystem:add({
                start = start,
                callback = function(value)
                    set_position(button, value, y)
                end,
                doneCallback = function()
                    if is_new then
                        add_new_score(obj, score)
                    end
                end,
            })

            return obj.added
        end
    end
    return "skip"
end

print(
    "regress_37_shared_terminal_closure_tail#1",
    show(make_obj(1, 2)),
    show(make_obj(4, 2))
)
