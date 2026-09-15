-- regress_363_nested_close_common_copy: a common copy may move after a nested close scope that already ended
-- 初始化常量保留原低槽前缀；这里检查的是分支末端的共同 COPY，不要求移动初始化。
-- unluac: expect-order [[label = "else"]] [[r2_2 = r2_0]]
-- unluac: expect-count [[r2_2 = r2_0]] [[1]]
-- unluac: expect-contains [[return r2_2]]
-- unluac: expect-ast-count [[close-binding]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]]

local close_log = {}
local close_meta = {
    __close = function(value)
        close_log[#close_log + 1] = value.label
    end,
}

local function run(flag)
    local assigned = "assigned"
    local result
    if flag then
        do
            local resource <close> = setmetatable({ label = "then" }, close_meta)
        end
        result = assigned
    else
        do
            local resource <close> = setmetatable({ label = "else" }, close_meta)
        end
        result = assigned
    end
    return result
end

assert(run(true) == "assigned")
assert(run(false) == "assigned")
assert(table.concat(close_log, ",") == "then,else")
