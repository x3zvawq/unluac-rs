local keys = { "left", "right" }
local t = {
    branches = {
        left = {
            score = 4,
        },
        right = {
            score = 9,
        },
    },
}

local selected = t.branches[keys[2]]
selected.score = selected.score + t.branches[keys[1]].score
t.branches[keys[1]].score = selected.score - 3

print("table-lookup", t.branches.left.score, t.branches.right.score, selected == t.branches.right)
