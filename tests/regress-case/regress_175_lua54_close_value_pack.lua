-- regress_175_lua54_close_value_pack#1: 多 binding 声明保留最后一个 <close> 属性
local close_log = {}
local close_meta = {
    __close = function(value)
        close_log[#close_log + 1] = value.label
    end,
}

do
    local function pair_with_close(label)
        return "plain", setmetatable({ label = label }, close_meta)
    end

    local plain, resource <close> = pair_with_close("declaration")
    print("regress_175_lua54_close_value_pack#1", plain, resource.label)
end
print("regress_175_lua54_close_value_pack#1-close", table.concat(close_log, ","))

-- regress_175_lua54_close_value_pack#2: generic-for 第四个固定表达式归 source pack 所有
local function iterator(state, control)
    local next_index = (control or 0) + 1
    if state[next_index] == nil then
        return nil
    end
    return next_index, state[next_index]
end

do
    local closing = setmetatable({ label = "generic-for" }, close_meta)
    for _, value in iterator, { "value" }, nil, closing do
        print("regress_175_lua54_close_value_pack#2", value)
    end
end
print("regress_175_lua54_close_value_pack#2-close", table.concat(close_log, ","))

-- regress_175_lua54_close_value_pack#3: 公共赋值不得越过 branch 内的隐式 close
local function assign_before_branch_close(flag)
    local assigned = "assigned"
    local result
    local branch_meta = {
        __close = function()
            close_log[#close_log + 1] = "branch:" .. tostring(result)
            result = "closed"
        end,
    }
    if flag then
        local resource <close> = setmetatable({}, branch_meta)
        result = assigned
    else
        local resource <close> = setmetatable({}, branch_meta)
        result = assigned
    end
    return result
end

assert(assign_before_branch_close(true) == "closed")
assert(assign_before_branch_close(false) == "closed")
print("regress_175_lua54_close_value_pack#3-close", table.concat(close_log, ","))
