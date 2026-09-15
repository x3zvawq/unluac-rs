// This file is part of unluac-rs and is licensed under the MIT License.
#include "lua.h"
#include "lualib.h"

#include <cstdio>
#include <cstring>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>

// Match the pinned CLI's explicit GC entry point: registered lifetime cases run
// the same observations against source and compiled chunks.
static int collectGarbage(lua_State* L)
{
    const char* option = luaL_optstring(L, 1, "collect");
    if (std::strcmp(option, "collect") == 0)
    {
        lua_gc(L, LUA_GCCOLLECT, 0);
        return 0;
    }
    if (std::strcmp(option, "count") == 0)
    {
        lua_pushnumber(L, lua_gc(L, LUA_GCCOUNT, 0));
        return 1;
    }
    luaL_error(L, "collectgarbage must be called with 'count' or 'collect'");
}

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
    if (argc != 2 && argc != 3)
    {
        fprintf(stderr, "Usage: luau-bytecode-runner <binary chunk> [observer chunk]\n");
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
    lua_pushcfunction(global, collectGarbage, "collectgarbage");
    lua_setglobal(global, "collectgarbage");
    luaL_sandbox(global);

    lua_State* thread = lua_newthread(global);
    luaL_sandboxthread(thread);

    std::string chunkname = "@" + std::string(argv[1]);
    int status = luau_load(thread, chunkname.c_str(), bytecode.data(), bytecode.size(), 0);
    int argumentCount = 0;
    if (status == 0 && argc == 3)
    {
        std::string observer = readBytecode(argv[2]);
        if (observer.empty())
        {
            fprintf(stderr, "Error opening observer bytecode %s\n", argv[2]);
            return 1;
        }
        status = luau_load(thread, "@runtime-observer", observer.data(), observer.size(), 0);
        if (status == 0)
        {
            // The observer receives the original loaded closure. Its environment edits do
            // not enter the source module or change that module's compiler decisions.
            lua_insert(thread, 1);
            argumentCount = 1;
        }
    }
    if (status == 0)
        status = lua_resume(thread, nullptr, argumentCount);

    return status == 0 ? 0 : reportError(thread, status);
}
