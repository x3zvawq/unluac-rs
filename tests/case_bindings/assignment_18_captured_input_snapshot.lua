-- 捕获 cell 在快照之前已由闭包改写；并行赋值仍读取当前值，不留下独立中转声明。
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=1]]
local function run()
    local value = {tag = "old"}
    local trace = "old"
    local current
    local function change()
        value = {tag = "new"}
    end
    local function observe()
        assert(current == value and current.tag == "new" and trace == "")
    end
    change()
    current, trace = value, ""
    observe()
    print("captured-input-snapshot", current.tag, trace)
end
run()
