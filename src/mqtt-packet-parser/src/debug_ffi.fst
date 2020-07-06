module Debug_FFI

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer

open FStar.HyperStack.ST

assume val print_hex_u8 (i:U8.t): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

assume val print_hex_u16 (i:U16.t): Stack unit
(requires (fun h -> true))
(ensures (fun h0 ret h1 -> true))

assume val print_buffer_u8: (buffer: B.buffer U8.t)
-> buffer_size: U32.t
-> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

assume val print_buffer_u16: (buffer: B.buffer U16.t)
-> buffer_size: U32.t
-> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))