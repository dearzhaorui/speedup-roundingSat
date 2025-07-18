cmake_minimum_required(VERSION 3.5)
project(RoundingSat2_beta)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")


file(GLOB ALL_CPP_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp)
file(GLOB ALL_HPP_FILES ${PROJECT_SOURCE_DIR}/src/*.hpp)
file(GLOB ALL_SRC_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp ${PROJECT_SOURCE_DIR}/src/*.hpp)

# uncomment to profile with gprof
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
#set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")

# uncomment to do something ugly
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Ofast")


set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra  ") # -DNDEBUG
set(BUILD_SHARED_LIBS ON)
#set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++ -static -lm -lz ")

# NEW LINE
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--copy-dt-needed-entries") # for reading gzlib file

add_executable(roundingsat ${ALL_CPP_FILES})

add_custom_target(release
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Release ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat -j 4
  COMMENT "Creating executable in release mode.")

add_custom_target(release_single
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Release ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat
  COMMENT "Creating executable in release mode.")

#sudo apt-get install zlibc zlib1g zlib1g-dev lib64z1 -y
find_package(ZLIB REQUIRED)
target_link_libraries(roundingsat PRIVATE ZLIB::ZLIB)

add_executable(roundingsat_debug ${ALL_CPP_FILES})

add_custom_target(debug
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Debug ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_debug -j 4
  COMMENT "Creating executable in debug mode.")

add_custom_target(debug_single
  COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=Debug ${CMAKE_SOURCE_DIR}
  COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_debug
  COMMENT "Creating executable in debug mode.")

add_executable(roundingsat_info ${ALL_CPP_FILES})

add_custom_target(info
        COMMAND ${CMAKE_COMMAND} -DCMAKE_BUILD_TYPE=RelWithDebInfo ${CMAKE_SOURCE_DIR}
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target roundingsat_info -j 4
        COMMENT "Creating executable in release mode with debug info.")

add_custom_target(
        format
        COMMAND /usr/bin/clang-format
        -style=file
        -i
        ${ALL_SRC_FILES}
        

)
