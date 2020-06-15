module Debug

open FStar.HyperStack.ST
open C
open LowStar.Printf

// TODO: 本番環境では削除
val unimplemented: (s: string) -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))
let unimplemented s = print_string "[Unmplemented]: "; print_string s; exit 1l