module Utils

open FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack

let zero_terminated_buffer_u8 (h: HS.mem) (b: B.buffer U8.t) =
  let s = B.as_seq h b in
  B.length b > 0 /\
  B.length b <= FStar.UInt.max_int 32 /\
  U8.v (Seq.index s (B.length b - 1)) = 0

assume val print_hex (i:U8.t): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

assume val topic_name_uint8_to_c_string: u8_buffer: B.buffer U8.t -> Stack C.String.t
  (requires (fun h -> B.live h u8_buffer /\ zero_terminated_buffer_u8 h u8_buffer /\ B.length u8_buffer = 65536))
  (ensures (fun h0 ret h1 -> U32.v (C.String.strlen ret) <= 65535))

assume val payload_uint8_to_c_string: u8_buffer: B.buffer U8.t -> packet_size: U32.t{U32.v packet_size >= 2} -> Stack C.String.t
  (requires (fun h ->
    B.live h u8_buffer /\ zero_terminated_buffer_u8 h u8_buffer /\ B.length u8_buffer = U32.v packet_size))
  (ensures (fun h0 ret h1 -> U32.v (C.String.strlen ret) <= U32.v (U32.sub packet_size 1ul)))