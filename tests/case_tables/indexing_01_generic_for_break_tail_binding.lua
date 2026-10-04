-- unluac: expect-ast-count [[generic-for]] [[3]]
-- unluac: expect-ast-count [[break]] [[2]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[table-constructor]] [[16]]
-- unluac: expect-ast-max [[local-binding]] [[16]]
-- regress_19_generic_for_break_tail_binding#1: generic-for break tail keeps loop bindings in scope
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[table.remove]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local registry = {}
local removed_index = 0

local objects = {
    world = {
        target = {
            name = "target",
            forceFields = {
                { forceFieldName = "old" },
                { forceFieldName = "source" },
            },
        },
        source = {
            forceField = true,
            uniformForceFieldType = "wind",
            forceX = 1,
            forceY = 2,
        },
        new = {
            forcePoint = true,
            uniformForceFieldType = "pull",
            force = 3,
            x = 4,
            y = 5,
        },
    },
}

local function field_names(fields)
    if fields == nil then
        return "nil"
    end

    local names = {}
    for index, field in ipairs(fields) do
        names[index] = field.forceFieldName
    end
    return table.concat(names, ",")
end

local function update_field(name, target_name, add)
    local source = objects.world[name]
    local target = objects.world[target_name]

    if add then
        if not registry["forceField" .. target_name] then
            registry["forceField" .. target_name] = function()
                return target.name
            end
        end

        if target.forceFields then
            local found = false
            for _, field in ipairs(target.forceFields) do
                if field.forceFieldName == name then
                    found = true
                    break
                end
            end

            if not found then
                if source.forceField then
                    target.forceFields[#target.forceFields + 1] = {
                        forceFieldName = name,
                        uniformForceFieldType = source.uniformForceFieldType,
                        forceX = source.forceX,
                        forceY = source.forceY,
                        field = true,
                    }
                elseif source.forcePoint then
                    target.forceFields[#target.forceFields + 1] = {
                        forceFieldName = name,
                        uniformForceFieldType = source.uniformForceFieldType,
                        force = source.force,
                        forceX = source.x,
                        forceY = source.y,
                        point = true,
                    }
                end
            end
        elseif source.forceField then
            target.forceFields = {
                {
                    forceFieldName = name,
                    uniformForceFieldType = source.uniformForceFieldType,
                    forceX = source.forceX,
                    forceY = source.forceY,
                    field = true,
                },
            }
        elseif source.forcePoint then
            target.forceFields = {
                {
                    forceFieldName = name,
                    uniformForceFieldType = source.uniformForceFieldType,
                    force = source.force,
                    forceX = source.x,
                    forceY = source.y,
                    point = true,
                },
            }
        end
    elseif target.forceFields then
        for index, field in ipairs(target.forceFields) do
            if field.forceFieldName == name then
                if registry["forceField" .. target_name] then
                    registry["forceField" .. target_name] = nil
                end
                table.remove(target.forceFields, index)
                removed_index = index
                break
            end
        end

        if #target.forceFields == 0 then
            target.forceFields = nil
        end
    end
end

update_field("new", "target", true)
update_field("source", "target", true)
update_field("old", "target", false)

assert(field_names(objects.world.target.forceFields) == "source,new")
assert(removed_index == 1 and registry.forceFieldtarget == nil)

print(
    "regress_19_generic_for_break_tail_binding#1",
    field_names(objects.world.target.forceFields),
    removed_index,
    registry.forceFieldtarget == nil
)

-- 尾部删除必须继续使用命中项的 index；旧列表别名也应观察同一次修改。
local fields = objects.world.target.forceFields
assert(fields[2].point and fields[2].force == 3)
assert(fields[2].uniformForceFieldType == "pull" and fields[2].forceX == 4 and fields[2].forceY == 5)
update_field("new", "target", false)
assert(removed_index == 2 and #fields == 1 and fields[1].forceFieldName == "source")
update_field("source", "target", false)
assert(#fields == 0 and objects.world.target.forceFields == nil)
assert(field_names(objects.world.target.forceFields) == "nil")

-- 列表不存在时分别建立 field/point；无匹配删除和重复添加不得破坏注册闭包。
update_field("source", "target", true)
fields = objects.world.target.forceFields
assert(#fields == 1 and fields[1].forceFieldName == "source" and fields[1].field)
assert(fields[1].uniformForceFieldType == "wind" and fields[1].forceX == 1 and fields[1].forceY == 2)
assert(registry.forceFieldtarget() == "target")
update_field("old", "target", false)
update_field("source", "target", true)
assert(#fields == 1 and registry.forceFieldtarget() == "target")
update_field("source", "target", false)
assert(objects.world.target.forceFields == nil and registry.forceFieldtarget == nil)
update_field("new", "target", true)
fields = objects.world.target.forceFields
assert(#fields == 1 and fields[1].forceFieldName == "new" and fields[1].point)
assert(fields[1].force == 3 and fields[1].forceX == 4 and fields[1].forceY == 5)
assert(fields[1].uniformForceFieldType == "pull" and registry.forceFieldtarget() == "target")
update_field("source", "target", true)
assert(#fields == 2 and fields[2].forceFieldName == "source" and fields[2].field)
assert(fields[2].uniformForceFieldType == "wind" and fields[2].forceX == 1 and fields[2].forceY == 2)
update_field("source", "target", false)
assert(#fields == 1 and removed_index == 2)
update_field("new", "target", false)
update_field("source", "target", false)
assert(objects.world.target.forceFields == nil and registry.forceFieldtarget == nil and removed_index == 1)
