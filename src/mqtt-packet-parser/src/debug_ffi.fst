module Debug_FFI

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer

open FStar.HyperStack.ST

assume val print_hex (i:U8.t): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

assume val print_buffer: (buffer: B.buffer U8.t)
-> buffer_size: U32.t
-> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))