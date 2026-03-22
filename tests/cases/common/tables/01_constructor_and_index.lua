local t = {
    1,
    2,
    3,
    label = "box",
    extra = 8,
}

t[2] = t[1] + t[3]

print("table", t[1], t[2], t[3], t.label, t.extra)
