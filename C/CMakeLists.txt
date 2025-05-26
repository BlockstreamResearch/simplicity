cmake_minimum_required(VERSION 3.16)

project(BitcoinSimplicity)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_EXTENSIONS OFF)

add_library(BitcoinSimplicity STATIC
  bitstream.c
  dag.c
  deserialize.c
  eval.c
  frame.c
  jets-secp256k1.c
  jets.c
  rsort.c
  sha256.c
  type.c
  typeInference.c
  bitcoin/env.c
  bitcoin/exec.c
  bitcoin/jets.c
  bitcoin/ops.c
  bitcoin/primitive.c
  bitcoin/txEnv.c
)

option(PRODUCTION "Enable production build" ON)
if (PRODUCTION)
  target_compile_definitions(BitcoinSimplicity PRIVATE "PRODUCTION")
endif()

target_include_directories(BitcoinSimplicity PUBLIC
                          "${PROJECT_SOURCE_DIR}/include"
                          )
