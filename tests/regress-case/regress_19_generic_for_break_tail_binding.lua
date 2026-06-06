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

print(
    "regress_19_generic_for_break_tail_binding#1",
    field_names(objects.world.target.forceFields),
    removed_index,
    registry.forceFieldtarget == nil
)
