local function recover_unlock_message(level)
    local needed = 0

    if level.feathers_required and level.feathers_required > 0 then
        local feathers = calculateFeatherScore(level.episode)
        needed = level.feathers_required - feathers
        consume(needed)
    elseif level.stars_required and level.stars_required > 0 then
        local stars = calculateEpisodeStars(level.episode)
        needed = level.stars_required - stars
        consume(needed)
    else
        needed = 0
        consume(needed)
    end

    local function on_unlock()
        return level.name, needed
    end

    return on_unlock
end

-- 分支返回的闭包应保存各自 needed，同时继续引用原 level 对象。
local consumed, score_calls = {}, {}
function calculateFeatherScore(episode)
    score_calls[#score_calls + 1] = "feathers:" .. episode
    return 3
end
function calculateEpisodeStars(episode)
    score_calls[#score_calls + 1] = "stars:" .. episode
    return 5
end
function consume(value)
    consumed[#consumed + 1] = value
end
local feather = { name = "feather", episode = "a", feathers_required = 10, stars_required = 20 }
local star = { name = "star", episode = "b", feathers_required = 0, stars_required = 8 }
local plain = { name = "plain", episode = "c" }
local f, s, p = recover_unlock_message(feather), recover_unlock_message(star), recover_unlock_message(plain)
assert(table.concat(score_calls, ",") == "feathers:a,stars:b")
assert(table.concat(consumed, ",") == "7,3,0")
feather.name, feather.feathers_required = "changed", 99
local fn, fv = f()
local sn, sv = s()
local pn, pv = p()
assert(fn == "changed" and fv == 7 and sn == "star" and sv == 3 and pn == "plain" and pv == 0)
print("regress_11_branch#1", fn, fv, sn, sv, pn, pv)

-- unluac: expect-contains [[return function()]]
-- unluac: expect-contains [[return p1_0.name, r1_0]]
-- unluac: expect-not-contains [[unluac error]]
