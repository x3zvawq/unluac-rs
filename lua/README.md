# Lua Toolchains

This directory stores vendored Lua-family toolchains used by the repository bootstrap.

Pinned sources:

- `lua5.1`: Lua 5.1.5
- `lua5.2`: Lua 5.2.4
- `lua5.3`: Lua 5.3.6
- `lua5.4`: Lua 5.4.8
- `lua5.5`: Lua 5.5.0
- `luajit`: LuaJIT `v2.1` pinned to commit `659a61693aa3b87661864ad0f12eee14c865cd7f`
- `luau`: Luau `0.713`

Generated layout:

- `lua/sources/<toolchain>`: extracted or cloned source tree
- `lua/build/<toolchain>`: built executables

Commands:

```bash
cargo lua list
cargo lua init
cargo lua build lua5.1
cargo lua build luajit
cargo lua build luau
cargo lua fetch all
cargo lua clean lua5.1
```

Outputs:

- stock Lua builds produce `lua` and `luac`
- `luajit` produces `luajit`, its bundled `jit/` modules, and a compatibility wrapper `luac` that runs `luajit -b`
- `luau` produces `luau`, `luau-analyze`, `luau-compile`, and `luau-bytecode`

Host prerequisites:

- `curl`
- `tar`
- `make`
- `git`
- a working C/C++ toolchain
