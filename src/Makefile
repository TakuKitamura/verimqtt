all:
	make test && sleep 3 && krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c && ./out/mqttPacketParser.out packet_example.bin

verify:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c && ./out/mqttPacketParser.out packet_example.bin

exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c && ./out/mqttPacketParser.out packet_example.bin

exec_silent:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/mqttPacketParser.out main.fst callMain.c utils.c > /dev/null 2>&1 && ./out/mqttPacketParser.out packet_example.bin

test_valid_packets:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c utils.c && \
	./out/testValidPackets.out

test_valid_packets_exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c utils.c && ./out/testValidPackets.out

test_slice_byte:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c utils.c && \
	./out/testSliceByte.out

test_slice_byte_exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c utils.c && ./out/testSliceByte.out

test_decoding_packets:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -o ./out/testDecodingPackets.out testDecodingPackets.fst testing.c utils.c && \
	./out/testDecodingPackets.out

test_decoding_packets_exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -o ./out/testDecodingPackets.out testDecodingPackets.fst testing.c utils.c && ./out/testDecodingPackets.out

test_error_handle:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c utils.c && \
	./out/testErrorHandle.out

test_error_handle_exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c utils.c && ./out/testErrorHandle.out

test:
	make test_valid_packets_exec && \
	make test_slice_byte_exec && \
	make test_decoding_packets_exec && \
	make test_error_handle_exec && \
	./out/testValidPackets.out && \
	./out/testSliceByte.out && \
	./out/testDecodingPackets.out && \
	./out/testErrorHandle.out