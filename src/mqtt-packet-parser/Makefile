# TODO: Makefile 修正
# TODO: Test 修正

all:
	cd src && \
	krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ../out -fsopt --cache_dir -fsopt ../out -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI -no-prefix Debug -no-prefix Debug_FFI -o ../mqttPacketParser.out main.fst common.fst const.fst publish.fst connect.fst disconnect.fst ffi.fst debug.fst debug_ffi.fst callMain.c ffi.c debug_ffi.c


all_exec:
	time (make test && sleep 3 && krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

mesure_verify_time:
	time (krml -warn-error +9 -verify -skip-extraction -skip-translation -skip-compilation -skip-linking -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

measure_time:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst measureTime.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

measure_time_optimize:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -ccopt -O3 -ccopt -mtune=native -ccopt -march=native -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst measureTime.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

measure_time_optimize_debug:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -ccopt -g -ccopt -O3 -ccopt -mtune=native -ccopt -march=native -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst measureTime.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

measure_time_debug:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -ccopt -g -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst measureTime.c utils.c && ./out/mqttPacketParser.out packet_example.bin)

verify:
	cd src && \
	time (krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ../out -fsopt --cache_dir -fsopt ../out -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI  -o ../mqttPacketParser.out main.fst common.fst const.fst publish.fst connect.fst disconnect.fst ffi.fst callMain.c ffi.c && ../mqttPacketParser.out ../bin/publish.bin)

compile:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c)

exec_silent:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c > /dev/null 2>&1 && ./out/mqttPacketParser.out packet_example.bin)

test_valid_packets:
	time (krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c utils.c && \
	./out/testValidPackets.out)

test_valid_packets_exec:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c utils.c && ./out/testValidPackets.out)

test_slice_byte:
	time (krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c utils.c && \
	./out/testSliceByte.out)

test_slice_byte_exec:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c utils.c && ./out/testSliceByte.out)

test_decoding_packets:
	time (krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -o ./out/testDecodingPackets.out testDecodingPackets.fst testing.c utils.c && \
	./out/testDecodingPackets.out)

test_decoding_packets_exec:
	cd src && \
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI -no-prefix Debug -o ./out/testDecodingPackets.out ./test/testDecodingPackets.fst ./test/testing.fst ffi.c ffi.fst ./test/testing.c && ./out/testDecodingPackets.out)

test_error_handle:
	time (krml -warn-error +9 -verify -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c utils.c && \
	./out/testErrorHandle.out)

test_error_handle_exec:
	time (krml -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c utils.c && ./out/testErrorHandle.out)

test:
	time (make test_valid_packets_exec && \
	make test_slice_byte_exec && \
	make test_decoding_packets_exec && \
	make test_error_handle_exec && \
	./out/testValidPackets.out && \
	./out/testSliceByte.out && \
	./out/testDecodingPackets.out && \
	./out/testErrorHandle.out)
