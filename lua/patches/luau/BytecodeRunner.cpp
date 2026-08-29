// This file is part of unluac-rs and is licensed under the MIT License.
#include "lua.h"
#include "lualib.h"

#include <cstdio>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>

static std::string readBytecode(const char* path)
{
    std::ifstream stream(path, std::ios::binary);
    if (!stream)
        return std::string();

    return std::string(std::istreambuf_iterator<char>(stream), std::istreambuf_iterator<char>());
}

static int reportError(lua_State* L, int status)
{
    std::string error;
    if (status == LUA_YIELD)
        error = "thread yielded unexpectedly";
    else if (const char* message = lua_tostring(L, -1))
        error = message;

    error += "\nstacktrace:\n";
    error += lua_debugtrace(L);
    fprintf(stderr, "%s", error.c_str());
    return 1;
}

int main(int argc, char** argv)
{
    if (argc != 2)
    {
        fprintf(stderr, "Usage: luau-bytecode-runner <binary chunk>\n");
        return 1;
    }

    std::string bytecode = readBytecode(argv[1]);
    if (bytecode.empty())
    {
        fprintf(stderr, "Error opening bytecode %s\n", argv[1]);
        return 1;
    }

    std::unique_ptr<lua_State, void (*)(lua_State*)> globalState(luaL_newstate(), lua_close);
    lua_State* global = globalState.get();
    luaL_openlibs(global);
    luaL_sandbox(global);

    lua_State* thread = lua_newthread(global);
    luaL_sandboxthread(thread);

    std::string chunkname = "@" + std::string(argv[1]);
    int status = luau_load(thread, chunkname.c_str(), bytecode.data(), bytecode.size(), 0);
    if (status == 0)
        status = lua_resume(thread, nullptr, 0);

    return status == 0 ? 0 : reportError(thread, status);
}
