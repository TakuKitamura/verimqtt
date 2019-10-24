all:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

exec:
	krml  -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

debug:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

test:
	krml -verify -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out

test_exec:
	krml -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -no-prefix TestValidPackets -o ./out/testValidPackets.out testValidPackets.fst testing.c fstarHelper.c && \
	./out/testValidPackets.out