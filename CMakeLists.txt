cmake_minimum_required(VERSION 3.19)
project(kaleidoscope
  VERSION 1.0
  DESCRIPTION "LLVM Tutorial"
  LANGUAGES CXX
  )

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(LLVM REQUIRED COMPONENTS LLVMSupportMeuPau)
llvm_map_components_to_libnames(LLVM_LIBS core passes support)

add_executable(k main.cpp)
target_compile_features(k PUBLIC cxx_std_20)
target_include_directories(k PUBLIC ${LLVM_INCLUDE_DIRS})
target_link_libraries(k PUBLIC ${LLVM_LIBS})
