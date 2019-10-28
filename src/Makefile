all:
	make test_exec && sleep 3 && krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

verify:
	krml -verify -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

exec:
	krml -warn-error +9 -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

test_valid_packets:
	krml -verify -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out

test_valid_packets_exec:
	krml -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && ./out/testValidPackets.out

test_slice_byte:
	krml -verify -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c fstarHelper.c && \
	./out/testSliceByte.out

test_slice_byte_exec:
	krml -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c fstarHelper.c && ./out/testSliceByte.out

test_decoding_packets:
	krml -verify -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -o ./out/testDecodingPackets.out testDecodingPackets.fst testing.c fstarHelper.c && \
	./out/testDecodingPackets.out

test_decoding_packets_exec:
	krml -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestDecodingPackets -o ./out/testDecodingPackets.out testDecodingPackets.fst testing.c fstarHelper.c && ./out/testDecodingPackets.out

test_error_handle:
	krml -verify -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c fstarHelper.c && \
	./out/testErrorHandle.out

test_error_handle_exec:
	krml -warn-error +9 -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestErrorHandle -o ./out/testErrorHandle.out testErrorHandle.fst testing.c fstarHelper.c && ./out/testErrorHandle.out

test_exec:
	make test_valid_packets_exec && \
	make test_slice_byte_exec && \
	make test_decoding_packets_exec && \
	make test_error_handle_exec && \
	./out/testValidPackets.out && \
	./out/testSliceByte.out && \
	./out/testDecodingPackets.out && \
	./out/testErrorHandle.out