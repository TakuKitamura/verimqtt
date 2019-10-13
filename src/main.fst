module Main

module B = LowStar.Buffer
module M = LowStar.Modifies
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
// module U32 = FStar.UInt32

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Printf
open FStar.Int.Cast

module U32 = FStar.UInt32
module U8 = FStar.UInt8

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901022
// 2.1.2 MQTT Control Packet type
// Table 2‑1 MQTT Control Packet types
type type_mqtt_control_packets = U8.t // Base 10

let define_mqtt_control_packet_RESERVED : type_mqtt_control_packets = 0uy
let define_mqtt_control_packet_CONNECT : type_mqtt_control_packets = 1uy
let define_mqtt_control_packet_CONNACK : type_mqtt_control_packets = 2uy
let define_mqtt_control_packet_PUBLISH : type_mqtt_control_packets = 3uy
let define_mqtt_control_packet_PUBACK : type_mqtt_control_packets = 4uy
let define_mqtt_control_packet_PUBREC : type_mqtt_control_packets = 5uy
let define_mqtt_control_packet_PUBREL : type_mqtt_control_packets = 6uy
let define_mqtt_control_packet_PUBCOMP : type_mqtt_control_packets = 7uy
let define_mqtt_control_packet_SUBSCRIBE : type_mqtt_control_packets = 8uy
let define_mqtt_control_packet_SUBACK : type_mqtt_control_packets = 9uy
let define_mqtt_control_packet_UNSUBSCRIBE : type_mqtt_control_packets = 10uy
let define_mqtt_control_packet_UNSUBACK : type_mqtt_control_packets = 11uy
let define_mqtt_control_packet_PINGREQ : type_mqtt_control_packets = 12uy
let define_mqtt_control_packet_PINGRESP : type_mqtt_control_packets = 13uy
let define_mqtt_control_packet_DISCONNECT : type_mqtt_control_packets = 14uy
let define_mqtt_control_packet_AUTH : type_mqtt_control_packets = 15uy


// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901022
// 2.1.3 Flags
// Table 2‑2 Flag Bits
type type_flags = U8.t // Base 2

let define_flag_CONNECT : type_flags = 0b0000uy
let define_flag_CONNACK : type_flags = 0b0000uy 
// PUBLISH のフラグは下記に記述
let define_flag_PUBACK : type_flags = 0b0000uy
let define_flag_PUBREC : type_flags = 0b0000uy
let define_flag_PUBREL : type_flags = 0b0010uy
let define_flag_PUBCOMP : type_flags = 0b0000uy
let define_flag_SUBSCRIBE : type_flags = 0b0010uy
let define_flag_SUBACK : type_flags = 0b0000uy
let define_flag_UNSUBSCRIBE : type_flags = 0b0010uy
let define_flag_UNSUBACK : type_flags = 0b0000uy
let define_flag_PINGREQ : type_flags = 0b0000uy
let define_flag_PINGRESP : type_flags = 0b0000uy
let define_flag_DISCONNECT : type_flags = 0b0000uy
let define_flag_AUTH : type_flags = 0b0000uy

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.1 DUP
type type_dup_flags = U8.t // Base 10

let define_dup_flag_first_delivery : type_dup_flags = 0uy
let define_dup_flag_re_delivery : type_dup_flags = 1uy 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.2 QoS
// Table 3‑2 - QoS definitions
type type_qos_flags = U8.t // Base 2

let define_qos_flag_at_most_once_delivery : type_qos_flags = 0b00uy
let define_qos_flag_at_least_once_delivery : type_qos_flags = 0b01uy
let define_qos_flag_exactly_once_delivery : type_qos_flags = 0b10uy
let define_qos_flag_reserved : type_qos_flags = 0b11uy

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.3 RETAIN
type type_retain_flags = U8.t // Base 10

let define_retain_flag_must_not_store_application_message : type_retain_flags = 0uy
let define_retain_flag_must_store_application_message : type_retain_flags = 1uy 


// debug tool
assume val extern_print_hex (i: U8.t{ 0 <= U8.v i /\ U8.v i <= 255}): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

// TODO: get~ もう少し､きれいにできそう

// ex. 0xab -> 0x0a TODO: rの定義域を追加
val get_most_significant_four_bit_for_one_byte: i:U8.t -> r:U8.t
let get_most_significant_four_bit_for_one_byte i = U8.shift_right i 4ul

// ex. 0xab -> 0x0b TODO: rの定義域を追加
val get_least_significant_four_bit_for_one_byte: i:U8.t -> r:U8.t
let get_least_significant_four_bit_for_one_byte i = U8.logand i 0x0fuy

// ex. 0b1010 -> 0b0001 TODO: rの定義域を追加
val get_most_significant_four_bit_for_four_bit: i:U8.t -> r:U8.t
let get_most_significant_four_bit_for_four_bit i = U8.shift_right i 3ul

// ex. 0b1010 -> 0b0000 TODO: rの定義域を追加
val get_least_significant_four_bit_for_four_bit: i:U8.t -> r:U8.t
let get_least_significant_four_bit_for_four_bit i = U8.logand i 0x01uy

// ex. 0b1010 -> 0b0000 TODO: rの定義域を追加
val get_center_two_bit_for_four_bit: i:U8.t -> r:U8.t
let get_center_two_bit_for_four_bit i = U8.shift_right (U8.logand i 0x06uy) 1ul 


// TODO: 値の条件チェックがいる
val decodeing_variable_bytes: ptr_for_decoding_packets: B.buffer U32.t 
  -> Stack U32.t //(remaining_length:U32.t{0 <= U32.v remaining_length && U32.v remaining_length <= 268435455})
    (requires fun h0 -> B.live h0 ptr_for_decoding_packets  /\ B.length ptr_for_decoding_packets = 4)
    (ensures fun _ _ _ -> true)
let decodeing_variable_bytes ptr_for_decoding_packets =
  push_frame ();
  let ptr_for_decoding_packet: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_for_remaining_length: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_status: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_multiplier: B.buffer U32.t = B.alloca 1ul 1ul in
  let inv h (i: nat) = B.live h ptr_for_decoding_packets /\ B.live h ptr_for_decoding_packet /\ B.live h ptr_for_remaining_length /\ B.live h ptr_multiplier /\ B.live h ptr_status in
  let body (i: U32.t{ 0 <= U32.v i && U32.v i < 4 }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let ptr_status_v = ptr_status.(0ul) in
      if (ptr_status_v = 0ul) then
        (
          let _ = ptr_for_decoding_packet.(0ul) <- ptr_for_decoding_packets.(i) in
          let decoding_packet_u32: U32.t = ptr_for_decoding_packet.(0ul) in
          let decoding_packet_u8: U8.t = uint32_to_uint8 decoding_packet_u32 in
          let ccc_u8: U8.t = U8.logand decoding_packet_u8 127uy in
          let ccc2_u8: U8.t = U8.logand decoding_packet_u8 128uy in 
          let ccc_u32: U32.t = uint8_to_uint32 ccc_u8 in

          // print_u32 ptr_for_remaining_length.(0ul);

          ptr_for_remaining_length.(0ul) <- 
            U32.(ptr_for_remaining_length.(0ul) +%^ (ptr_multiplier.(0ul) *%^ ccc_u32));
          
          ptr_multiplier.(0ul) <- U32.(ptr_multiplier.(0ul) *%^ 128ul);

          if (ccc2_u8 = 0uy) then
            ptr_status.(0ul) <- 1ul
        )
      else 
        (
          if (i = 3ul && ptr_status_v = 0ul) then
            ptr_status.(0ul) <- 2ul
        )
  in
  C.Loops.for 0ul 4ul inv body;
  let r: U32.t = ptr_for_remaining_length.(0ul) in
  let s: U32.t = ptr_status.(0ul) in
  pop_frame ();
  if (s = 1ul) then
    (
      r
    )
  else
    (
      // TODO: エラー処理をどうするか
      print_string "malformed variable byte integer\n";
      0ul
    )

// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (msg byte) = 25
// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (23byte) = 25
// (1byte) + (1byte) + (23byte) = 25

// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (msg byte) = 100016
// x (1byte) + (msg len byte 1 or 2 or 3 or 4) + (172byte) = 100016
// x (1byte) + (msg len byte 2 or 3 or 4) + (34476byte) = 100016
// x (1byte) + (msg len byte 3 or 4) + (100012byte) = 100016
// (1byte) + (3byte) + (100012byte) = 100016

// TODO: 値域の設定
val get_remaining_length: i:U8.t -> ptr_for_decoding_packets: B.buffer U32.t -> packet_size:U32.t{1 <= U32.v packet_size}
  -> Stack U32.t
  (requires fun h0 -> B.live h0 ptr_for_decoding_packets /\ B.length ptr_for_decoding_packets = 4)
  (ensures fun _ _ _ -> true)
let get_remaining_length i ptr_for_decoding_packets packet_size = 
  push_frame ();
  let fixed_value = U32.(packet_size -^ 1ul) in 
  let rr =
  (
    if (i = 1uy) then
      (
        let decoding_packet_first: U32.t = ptr_for_decoding_packets.(0ul) in
        let decoding_packets = B.alloca 0ul 4ul in
        decoding_packets.(0ul) <- decoding_packet_first;
        let r: U32.t = decodeing_variable_bytes decoding_packets in
          if (U32.(1ul +%^ r) = fixed_value) then
            r
          else
            (
              // print_string("first bit is not remaining length");
              0ul
            )
      )
    else if (i = 2uy) then
      (
        let decoding_packet_first: U32.t = ptr_for_decoding_packets.(0ul) in
        let decoding_packet_second: U32.t = ptr_for_decoding_packets.(1ul) in
        let decoding_packets = B.alloca 0ul 4ul in
        decoding_packets.(0ul) <- decoding_packet_first;
        decoding_packets.(1ul) <- decoding_packet_second;
        let r = decodeing_variable_bytes decoding_packets in
          if (U32.(2ul +%^ r) = fixed_value) then
            r
          else
            (
              // print_string("first bit is not remaining length");
              0ul
            )
      )
    else if (i = 3uy) then
      (
        let decoding_packet_first: U32.t = ptr_for_decoding_packets.(0ul) in
        let decoding_packet_second: U32.t = ptr_for_decoding_packets.(1ul) in
        let decoding_packet_third: U32.t = ptr_for_decoding_packets.(2ul) in
        let decoding_packets = B.alloca 0ul 4ul in
        decoding_packets.(0ul) <- decoding_packet_first;
        decoding_packets.(1ul) <- decoding_packet_second;
        decoding_packets.(2ul) <- decoding_packet_third;
        let r = decodeing_variable_bytes decoding_packets in
          if (U32.(3ul +%^ r) = fixed_value) then
            r
          else
            (
              // print_string("first bit is not remaining length");
              0ul
            )
      )
    else if (i = 4uy) then
      (
        let r = decodeing_variable_bytes ptr_for_decoding_packets in
          if (U32.(4ul +%^ r) = fixed_value) then
            r
          else
            (
              // print_string("first bit is not remaining length");
              0ul
            )
      )
    else
      (0ul)
  ) in
  pop_frame ();
  rr

// TODO: PUBLISH の場合どう扱うか検討
type struct_fixed_header = {
  message_type: U8.t;
  dup_flag: U8.t;
  qos_flag: U8.t;
  retain_flag: U8.t;
  remaining_length: U32.t;
}

val bytes_loop: src:B.buffer U8.t -> len:U32.t -> Stack struct_fixed_header
  (requires fun h0 -> B.live h0 src /\ B.length src = U32.v len )
  (ensures fun _ _ _ -> true)
let bytes_loop src len =
  push_frame ();
  let ptr_message_type: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_flags: B.buffer U32.t  = B.alloca 0ul 1ul in
  let ptr_status: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_for_decoding_packets: B.buffer U32.t = B.alloca 0ul 4ul in
  let ptr_remaining_length: B.buffer U32.t  = B.alloca 0ul 1ul in
  let inv h (i: nat) = B.live h src /\
   B.live h ptr_message_type /\
  B.live h ptr_flags /\ B.live h ptr_for_decoding_packets /\ B.live h ptr_status /\ B.live h ptr_remaining_length in
  let body (i: U32.t{ 0 <= U32.v i && U32.v i < U32.v len }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let one_byte : U8.t = src.(i) in
      let one_byte_u32 : U32.t = uint8_to_uint32 one_byte in
        let ptr_status_v: U32.t = ptr_status.(0ul) in
      if (i = 0ul) then
        (
          ptr_message_type.(0ul) <- uint8_to_uint32 (get_most_significant_four_bit_for_one_byte one_byte);
          ptr_flags.(0ul) <- uint8_to_uint32 (get_least_significant_four_bit_for_one_byte one_byte)
        )
      else if (i = 1ul) then
        (
          ptr_for_decoding_packets.(0ul) <- one_byte_u32;
          let r = get_remaining_length 1uy ptr_for_decoding_packets len in
          if (U32.gt r 0ul) then
            (
              ptr_status.(0ul) <- 1ul;
              ptr_remaining_length.(0ul) <- r
            )
        )
      else if (i = 2ul) then
        (
          if (ptr_status_v = 0ul) then 
            (
              ptr_for_decoding_packets.(1ul) <- one_byte_u32;
              let r = get_remaining_length 2uy ptr_for_decoding_packets len in
              if (U32.gt r 0ul) then
                (
                  ptr_status.(0ul) <- 1ul;
                  ptr_remaining_length.(0ul) <- r
                )
            )
        )
      else if (i = 3ul) then
        (
          if (ptr_status_v = 0ul) then 
            (
              ptr_for_decoding_packets.(2ul) <- one_byte_u32;
              let r = get_remaining_length 3uy ptr_for_decoding_packets len in
              if (U32.gt r 0ul) then
                (
                  ptr_status.(0ul) <- 1ul;
                  ptr_remaining_length.(0ul) <- r
                )
            )
        )
      else if (i = 4ul) then
        (
          if (ptr_status_v = 0ul) then 
            (
              ptr_for_decoding_packets.(3ul) <- one_byte_u32;
              let r = get_remaining_length 4uy ptr_for_decoding_packets len in
              if (U32.gt r 0ul) then
                (
                  ptr_status.(0ul) <- 1ul;
                  ptr_remaining_length.(0ul) <- r
                )
              else 
                (
                  ptr_status.(0ul) <- 2ul
                )
            )
        )  
  in
  C.Loops.for 0ul len inv body;
  let message_type_u32: U32.t = ptr_message_type.(0ul) in
  let message_type_u8: U8.t = uint32_to_uint8 message_type_u32 in
  let flags_u32: U32.t = ptr_flags.(0ul) in
  let flags_u8: U8.t = uint32_to_uint8 flags_u32 in
  let remaining_length_u32: U32.t = ptr_remaining_length.(0ul) in
  let data: struct_fixed_header = {
    message_type = message_type_u8;
    dup_flag = get_most_significant_four_bit_for_four_bit flags_u8;
    qos_flag = get_center_two_bit_for_four_bit flags_u8;
    retain_flag = get_least_significant_four_bit_for_four_bit flags_u8;
    remaining_length = remaining_length_u32;
  } in
  pop_frame ();
  (* return *) data

val parse (request: B.buffer U8.t) (len: U32.t):
  Stack struct_fixed_header 
    (requires (fun h ->
      B.live h request /\
      B.length request = U32.v len  ))
    (ensures (fun h0 _ h1 ->
      B.live h1 request))
let parse request len =
    push_frame ();
    let data: struct_fixed_header = bytes_loop request len in
    pop_frame ();
    data