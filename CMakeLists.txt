cmake_minimum_required(VERSION 3.19)
project(kaleidoscope
  VERSION 1.0
  DESCRIPTION "LLVM Tutorial"
  LANGUAGES CXX
  )

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_path(LLVM_INC_DIR llvm/IR/Value.h)
find_library(LLVM_LIB REQUIRED)

add_executable(k main.cpp)
target_compile_features(k PUBLIC cxx_std_20)
target_include_directories(k PUBLIC ${LLVM_INC_DIR})
target_link_libraries(k PUBLIC ${LLVM_LIB})
