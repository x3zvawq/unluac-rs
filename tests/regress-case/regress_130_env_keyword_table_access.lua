-- regress_130_env_keyword_table_access#1: 环境表关键字 key 不能生成非法裸 global
-- unluac: expect-contains [[_ENV["end"]]
-- unluac: expect-not-contains [[end = 7]]
-- unluac: expect-not-contains [[unluac error]]
_ENV["end"] = 7
print("regress_130_env_keyword_table_access#1", _ENV["end"])
