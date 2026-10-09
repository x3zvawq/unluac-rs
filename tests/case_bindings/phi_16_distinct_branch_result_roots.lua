-- 两个仍存活的分支结果不能都复用唯一被覆盖的旧 CALL 根；输出观察两个对象身份。
local keys = {'one','two'}
function show(list,kind)
    for index,item in ipairs(list) do
        local root = item
        local hot = index == 1
        local hotBox
        if hot then hotBox = root:Lookup('hot_' .. keys[kind])
        else hotBox = root:Lookup('normal_' .. keys[kind]) end
        hotBox:Show(item.id == GetId())
        local first,second
        if hot then
            first = root:Lookup('rare_h_' .. keys[kind])
            second = root:Lookup('bg_h_' .. keys[kind])
        else
            first = root:Lookup('rare_' .. keys[kind])
            second = root:Lookup('bg_' .. keys[kind])
        end
        first:Show(item.rare > 0)
        second:Show(item.rare > 0)
    end
end

function GetId() return 1 end
local function object(name)
    local result = {name=name,rare=2,id=1}
    function result:Lookup(key) return object(self.name .. '/' .. key) end
    function result:Show(value) print(self.name, tostring(value)) end
    return result
end
show({object('row1'),object('row2')},1)
