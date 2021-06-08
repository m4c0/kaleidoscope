cmake_minimum_required(VERSION 3.19)
project(kaleidoscope
  VERSION 1.0
  DESCRIPTION "LLVM Tutorial"
  LANGUAGES CXX
  )

add_executable(k main.cpp)
target_compile_features(k PUBLIC cxx_std_20)
