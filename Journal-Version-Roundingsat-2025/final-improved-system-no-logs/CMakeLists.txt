cmake_minimum_required(VERSION 3.5)
project(RoundingSat2)

set(CMAKE_CXX_STANDARD 20)
INCLUDE(CheckCXXSourceCompiles)

if(CMAKE_BUILD_TYPE MATCHES "Debug")
    set(RS_STACKTRACE_COMPONENTS stacktrace_basic stacktrace_backtrace stacktrace_addr2line stacktrace_noop)
endif()

# Feel free to decrease the required boost version if you can verify that it works with
# a smaller version. It is known not to compile with version 1.53.0 and lower.
find_package(Boost 1.67 REQUIRED OPTIONAL_COMPONENTS iostreams ${RS_STACKTRACE_COMPONENTS})
include_directories(${Boost_INCLUDE_DIRS})
set(RS_Boost_LIBRARIES ${Boost_LIBRARIES})

if(Boost_IOSTREAMS_FOUND)
    set(CMAKE_REQUIRED_INCLUDES ${Boost_INCLUDE_DIRS})
    set(CMAKE_REQUIRED_LIBRARIES ${Boost_LIBRARIES})
    check_cxx_source_compiles(
            "#include <boost/iostreams/filter/gzip.hpp>
       int main() { auto decomp = boost::iostreams::gzip_decompressor(); (void)decomp; return 0; }"
            IOSTREAMS_WITH_ZLIB )
    check_cxx_source_compiles(
            "#include <boost/iostreams/filter/bzip2.hpp>
       int main() { auto decomp = boost::iostreams::bzip2_decompressor(); (void)decomp; return 0; }"
            IOSTREAMS_WITH_BZIP2 )
    check_cxx_source_compiles(
            "#include <boost/iostreams/filter/lzma.hpp>
       int main() { auto decomp = boost::iostreams::lzma_decompressor(); (void)decomp; return 0; }"
            IOSTREAMS_WITH_LZMA )
    check_cxx_source_compiles(
            "#include <boost/iostreams/filter/zstd.hpp>
       int main() { auto decomp = boost::iostreams::zstd_decompressor(); (void)decomp; return 0; }"
            IOSTREAMS_WITH_ZSTD )
endif()

configure_file("${PROJECT_SOURCE_DIR}/src/CMakeConfig.hpp.in" "${PROJECT_SOURCE_DIR}/src/CMakeConfig.hpp")

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")

if(NOT CMAKE_BUILD_TYPE)
    message(WARNING "Please use -DCMAKE_BUILD_TYPE=[build_type] where [build_type] is one of: Debug, Release, RelWithDebInfo and MinSizeRel")
endif()

set(build_static "OFF"
    CACHE STRING "Build and use static libraries.")

set(profile_flags "OFF"
    CACHE STRING "Build using gprof flag (-pg).")

set(soplex "OFF"
    CACHE STRING "Use SoPlex to check for rational infeasibility.")

set(soplex_pkg "https://github.com/scipopt/soplex/archive/refs/tags/release-711.tar.gz"
    CACHE STRING "SoPlex package, download from https://github.com/scipopt/soplex/")

set(gmp "OFF"
    CACHE STRING "Use GMP instead of Boost's builtin multiple precision integer.")

set(testruns_timeout 1
    CACHE STRING "Timeout of individual test runs.")

IF(soplex)
    # provides libsoplex and ${SOPLEX_INCLUDE_DIRS}
    include(${PROJECT_SOURCE_DIR}/cmake/soplex_build_and_load.cmake)
endif()

if(gmp)
    find_package(GMP REQUIRED)
    include_directories(${GMP_INCLUDE_DIR})
endif()

if(${build_static})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libgcc -static-libstdc++ -static")
endif()

if(${profile_flags})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")
endif()

# Get the current working branch
execute_process(
    COMMAND git rev-parse --abbrev-ref HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_BRANCH
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

# Get the latest abbreviated commit hash of the working branch
execute_process(
    COMMAND git log -1 --format=%h
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE
)
configure_file("${PROJECT_SOURCE_DIR}/src/version.hpp.in" "${PROJECT_SOURCE_DIR}/src/version.hpp")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

set(source_files
    src/Constr.cpp
    src/ConstrExp.cpp
    src/ConstrExpPool.cpp
    src/ConstrSimple.cpp
    src/Env.cpp
    src/Logger.cpp
    src/LpSolver.cpp
    src/ProofBuffer.cpp
    src/Solver.cpp
    src/SolverStructs.cpp
    src/Stats.cpp
    src/io.cpp
    src/objrewrite.cpp
    src/optimize.cpp
    src/parsing.cpp
    src/quit.cpp
    src/roundingsat.cpp
    src/run.cpp
    src/used_licenses/gpl_3_0.cpp
    src/used_licenses/apache_2.cpp
    src/used_licenses/roundingsat.cpp
    src/used_licenses/MIT.cpp
    src/used_licenses/licenses.cpp
    src/used_licenses/boost.cpp
    src/used_licenses/lgpl_3_0.cpp
)

set(header_files
    src/Constr.hpp
    src/Config.hpp
    src/ConstrExp.hpp
    src/ConstrExpPool.hpp
    src/ConstrSimple.hpp
    src/Env.hpp
    src/SolverStructs.hpp
    src/Logger.hpp
    src/ProofBuffer.hpp
    src/Stats.hpp
    src/LpSolver.hpp
    src/Options.hpp
    src/IntSet.hpp
    src/Solver.hpp
    src/typedefs.hpp
    src/auxiliary.hpp
    src/auxlog.hpp
    src/auxmath.hpp
    src/auxtime.hpp
    src/globals.hpp
    src/io.hpp
    src/objrewrite.hpp
    src/optimize.hpp
    src/parsing.hpp
    src/quit.hpp
    src/run.hpp
    src/used_licenses/roundingsat.hpp
    src/used_licenses/lgpl_3_0.hpp
    src/used_licenses/boost.hpp
    src/used_licenses/MIT.hpp
    src/used_licenses/gpl_3_0.hpp
    src/used_licenses/apache_2.hpp
    src/used_licenses/licenses.hpp
)

set(all_files ${source_files} ${header_files})

add_executable(roundingsat ${source_files})
target_include_directories(roundingsat PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})
target_link_libraries(roundingsat ${RS_Boost_LIBRARIES})

install(TARGETS roundingsat RUNTIME DESTINATION bin)

IF(soplex)
    target_link_libraries(roundingsat libsoplex)
    target_compile_definitions(roundingsat PUBLIC WITHSOPLEX)
endif()

IF(gmp)
    target_link_libraries(roundingsat gmp gmpxx)
    target_compile_definitions(roundingsat PUBLIC WITHGMP)
endif()

if(Boost_STACKTRACE_BASIC_FOUND)
    target_compile_definitions(roundingsat PUBLIC WITHSTACKTRACE)
    target_link_libraries(roundingsat ${CMAKE_DL_LIBS})
endif()

FIND_PROGRAM(CLANG_FORMAT "clang-format")

IF(CLANG_FORMAT)
    add_custom_target(
        format
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        COMMAND ${CLANG_FORMAT}
        -style=file
        -i
        ${all_files}
    )
endif()

add_custom_target(
    testruns
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/test
    COMMAND ./run_tests.sh ${testruns_timeout} "testruns" ${CMAKE_CURRENT_BINARY_DIR}/roundingsat
)
add_dependencies(testruns roundingsat)
