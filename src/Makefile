all:
	make test_exec && krml -verify -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

exec:
	krml  -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix Main -o ./out/main.out main.fst callMain.c fstarHelper.c && ./out/main.out

test:
	krml -verify -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out

test_exec:
	krml -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -fsopt --cache_dir -fsopt ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out