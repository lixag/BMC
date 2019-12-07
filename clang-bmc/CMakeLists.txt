add_clang_executable(clang-bmc ClangBMC.cc)

target_link_libraries(clang-bmc PRIVATE clangTooling)
