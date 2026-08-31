cmake_minimum_required(VERSION 3.10)
project(unluac_luau_bytecode_runner LANGUAGES CXX C)

if(NOT LUAU_SOURCE_DIR)
    message(FATAL_ERROR "LUAU_SOURCE_DIR must point to the pinned Luau source tree")
endif()

set(LUAU_BUILD_CLI ON CACHE BOOL "" FORCE)
set(LUAU_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(LUAU_BUILD_WEB OFF CACHE BOOL "" FORCE)
add_subdirectory("${LUAU_SOURCE_DIR}" luau)

add_executable(Luau.BytecodeRunner.CLI BytecodeRunner.cpp)
set_target_properties(Luau.BytecodeRunner.CLI PROPERTIES OUTPUT_NAME luau-bytecode-runner)
target_compile_features(Luau.BytecodeRunner.CLI PRIVATE cxx_std_17)
target_include_directories(Luau.BytecodeRunner.CLI PRIVATE "${LUAU_SOURCE_DIR}/VM/include")
target_link_libraries(Luau.BytecodeRunner.CLI PRIVATE Luau.VM)
