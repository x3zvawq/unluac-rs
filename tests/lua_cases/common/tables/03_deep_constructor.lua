local t = {
    root = {
        nodes = {
            {
                id = "a",
                values = { 1, 2 },
            },
            {
                id = "b",
                values = { 3, 4 },
            },
        },
        flags = {
            open = true,
            closed = false,
        },
    },
}

t.root.nodes[2].values[1] = t.root.nodes[1].values[2] + 5

print("deep-table", t.root.nodes[1].id, t.root.nodes[2].values[1], t.root.flags.open, #t.root.nodes)
