-- regress_131_lua55_anonymous_vararg#1: PF_VAHID 不能伪装成命名变参
-- unluac: expect-contains [[function(...)]]
-- unluac: expect-not-contains [[function(...r]]
return function(...)
    return ...
end
