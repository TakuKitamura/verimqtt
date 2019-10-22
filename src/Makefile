all:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

exec:
	krml  -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out

debug:
	krml -verify -drop WasmSupport -tmpdir ./out -no-prefix Main -fsopt --query_stats main.fst callMain.c fstarHelper.c && ./a.out
test:
	krml -add-include '"Testing.h"' -verify -drop WasmSupport -tmpdir ./out -no-prefix Test -fsopt --query_stats test.fst testing.c && ./a.out