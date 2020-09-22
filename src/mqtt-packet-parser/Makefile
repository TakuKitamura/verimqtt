# TODO: Makefile 修正
# TODO: Test 修正

SHELL=/bin/bash
CC=~/afl-2.52b/afl-gcc
all:
	cd src && \
	time krml -verbose -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ../out -fsopt --cache_dir -fsopt ../out -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI -no-prefix Debug -no-prefix Debug_FFI -o ../mqttPacketParser.out main.fst common.fst const.fst publish.fst connect.fst disconnect.fst ffi.fst debug.fst debug_ffi.fst callMain.c ffi.c debug_ffi.c

verify:
	cd src && \
	time krml -verify -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ../out -fsopt --cache_dir -fsopt ../out -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI -no-prefix Debug -no-prefix Debug_FFI -o ../mqttPacketParser.out main.fst common.fst const.fst publish.fst connect.fst disconnect.fst ffi.fst debug.fst debug_ffi.fst callMain.c ffi.c debug_ffi.c