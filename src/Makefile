all:
	make test_exec && sleep 3 && krml -verify -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

exec:
	krml  -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

test_valid_packets:
	krml -verify -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out

test_valid_packets_exec:
	krml -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c

test_slice_byte:
	krml -verify -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c fstarHelper.c && \
	./out/testSliceByte.out

test_slice_byte_exec:
	krml -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestSliceByte -o ./out/testSliceByte.out testSliceByte.fst testing.c fstarHelper.c

test_exec:
	make test_valid_packets_exec && make test_slice_byte_exec && ./out/testValidPackets.out && ./out/testSliceByte.out