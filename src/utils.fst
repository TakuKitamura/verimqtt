module Utils

open FStar.HyperStack.ST
module U8 = FStar.UInt8

assume val print_hex (i:U8.t): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))