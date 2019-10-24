all:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

exec:
	krml  -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

debug:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

test:
	krml -verify -add-include '"Testing.h"' -silent -drop WasmSupport -tmpdir ./out -fsopt --silent -no-prefix TestValidPackets1 -o ./out/testValidPackets1.out testValidPackets1.fst testing.c fstarHelper.c && \
	krml -verify -add-include '"Testing.h"' -silent -drop WasmSupport -tmpdir ./out -fsopt --silent -no-prefix TestValidPackets2 -o ./out/testValidPackets2.out testValidPackets2.fst testing.c fstarHelper.c && \
	./out/testValidPackets1.out && \
	./out/testValidPackets2.out

exec_test:
	krml -add-include '"Testing.h"' -drop WasmSupport -tmpdir ./out -no-prefix Test -fsopt --query_stats test.fst testing.c fstarHelper.c && ./a.out