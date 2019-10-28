module Main

module B = LowStar.Buffer
module M = LowStar.Modifies
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Printf
open FStar.Int.Cast

module U32 = FStar.UInt32
module U8 = FStar.UInt8

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 30"

inline_for_extraction noextract
let (!$) = C.String.of_literal

val max_u32: U32.t
let max_u32 = 4294967295ul

val max_u8: U8.t
let max_u8 = 255uy

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

type type_mqtt_control_packet_label = C.String.t
let define_mqtt_control_packet_RESERVED_label : type_mqtt_control_packet_label = !$"RESERVED"
let define_mqtt_control_packet_CONNECT_label : type_mqtt_control_packet_label = !$"CONNECT"
let define_mqtt_control_packet_CONNACK_label : type_mqtt_control_packet_label = !$"CONNACK"
let define_mqtt_control_packet_PUBLISH_label : type_mqtt_control_packet_label = !$"PUBLISH"
let define_mqtt_control_packet_PUBACK_label : type_mqtt_control_packet_label = !$"PUBACK"
let define_mqtt_control_packet_PUBREC_label : type_mqtt_control_packet_label = !$"PUBREC"
let define_mqtt_control_packet_PUBREL_label : type_mqtt_control_packet_label = !$"PUBREL"
let define_mqtt_control_packet_PUBCOMP_label : type_mqtt_control_packet_label = !$"PUBCOMP"
let define_mqtt_control_packet_SUBSCRIBE_label : type_mqtt_control_packet_label = !$"SUBSCRIBE"
let define_mqtt_control_packet_SUBACK_label : type_mqtt_control_packet_label = !$"SUBACK"
let define_mqtt_control_packet_UNSUBSCRIBE_label : type_mqtt_control_packet_label = !$"UNSUBSCRIBE"
let define_mqtt_control_packet_UNSUBACK_label : type_mqtt_control_packet_label = !$"UNSUBACK"
let define_mqtt_control_packet_PINGREQ_label : type_mqtt_control_packet_label = !$"PINGREQ"
let define_mqtt_control_packet_PINGRESP_label : type_mqtt_control_packet_label = !$"PINGRESP"
let define_mqtt_control_packet_DISCONNECT_label : type_mqtt_control_packet_label = !$"DISCONNECT"
let define_mqtt_control_packet_AUTH_label : type_mqtt_control_packet_label = !$"AUTH"
type type_message_name_restrict =
  v:type_mqtt_control_packet_label{
    v = define_mqtt_control_packet_RESERVED_label ||
    v = define_mqtt_control_packet_CONNECT_label ||
    v = define_mqtt_control_packet_CONNACK_label ||
    v = define_mqtt_control_packet_PUBLISH_label ||
    v = define_mqtt_control_packet_PUBACK_label ||
    v = define_mqtt_control_packet_PUBREC_label ||
    v = define_mqtt_control_packet_PUBREL_label ||
    v = define_mqtt_control_packet_PUBCOMP_label ||
    v = define_mqtt_control_packet_SUBSCRIBE_label ||
    v = define_mqtt_control_packet_SUBACK_label ||
    v = define_mqtt_control_packet_UNSUBSCRIBE_label ||
    v = define_mqtt_control_packet_UNSUBACK_label ||
    v = define_mqtt_control_packet_PINGREQ_label ||
    v = define_mqtt_control_packet_PINGRESP_label ||
    v = define_mqtt_control_packet_DISCONNECT_label ||
    v = define_mqtt_control_packet_AUTH_label ||
    v = !$""
  }
val is_valid_message_type_check: message_type: U8.t -> r:U8.t
let is_valid_message_type_check message_type =
  if (U8.eq message_type define_mqtt_control_packet_RESERVED) then
    1uy
  else if (message_type <> define_mqtt_control_packet_CONNECT &&
      message_type <> define_mqtt_control_packet_CONNACK &&
      message_type <> define_mqtt_control_packet_PUBLISH &&
      message_type <> define_mqtt_control_packet_PUBACK &&
      message_type <> define_mqtt_control_packet_PUBREC &&
      message_type <> define_mqtt_control_packet_PUBREL &&
      message_type <> define_mqtt_control_packet_PUBCOMP &&
      message_type <> define_mqtt_control_packet_SUBSCRIBE &&
      message_type <> define_mqtt_control_packet_SUBACK &&
      message_type <> define_mqtt_control_packet_UNSUBSCRIBE &&
      message_type <> define_mqtt_control_packet_UNSUBACK &&
      message_type <> define_mqtt_control_packet_PINGREQ &&
      message_type <> define_mqtt_control_packet_PINGRESP &&
      message_type <> define_mqtt_control_packet_DISCONNECT &&
      message_type <> define_mqtt_control_packet_AUTH
  ) then
    2uy
  else
    0uy

type type_mqtt_control_packets_restrict =
  v:type_mqtt_control_packets{U8.eq (is_valid_message_type_check v) 0uy || U8.eq v max_u8}


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

val is_valid_dup_flag: dup_flag:type_dup_flags -> (r:U8.t{U8.v r <= 1})
let is_valid_dup_flag dup_flag =
  if (dup_flag <> define_dup_flag_first_delivery &&
      dup_flag <> define_dup_flag_re_delivery) then
    1uy
  else
    0uy

type type_dup_flags_restrict =
  dup_flag: type_dup_flags{U8.eq (is_valid_dup_flag dup_flag) 0uy || U8.eq dup_flag max_u8}

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.2 QoS
// Table 3‑2 - QoS definitions
type type_qos_flags = U8.t // Base 2

let define_qos_flag_at_most_once_delivery : type_qos_flags = 0b00uy
let define_qos_flag_at_least_once_delivery : type_qos_flags = 0b01uy
let define_qos_flag_exactly_once_delivery : type_qos_flags = 0b10uy
let define_qos_flag_reserved : type_qos_flags = 0b11uy

val is_valid_qos_flag: qos_flag:type_qos_flags -> (r:U8.t{U8.v r <= 1})
let is_valid_qos_flag qos_flag =
  if (qos_flag <> define_qos_flag_at_least_once_delivery &&
      qos_flag <> define_qos_flag_at_most_once_delivery &&
      qos_flag <> define_qos_flag_exactly_once_delivery) then
    1uy
  else
    0uy

type type_qos_flags_restrict =
  qos_flag: type_qos_flags{U8.eq (is_valid_qos_flag qos_flag) 0uy || U8.eq qos_flag max_u8}

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.3 RETAIN
type type_retain_flags = U8.t // Base 10

let define_retain_flag_must_not_store_application_message : type_retain_flags = 0uy
let define_retain_flag_must_store_application_message : type_retain_flags = 1uy

val is_valid_retain_flag: retain_flag:type_retain_flags -> (r:U8.t{U8.v r <= 1})
let is_valid_retain_flag retain_flag =
  if (retain_flag <> define_retain_flag_must_not_store_application_message &&
      retain_flag <> define_retain_flag_must_store_application_message) then
    1uy
  else
    0uy

type type_retain_flags_restrict =
  retain_flag: type_retain_flags{U8.eq (is_valid_retain_flag retain_flag) 0uy || U8.eq retain_flag max_u8}

type type_flag_restrict =
  flag: U8.t{
    U8.eq flag 0b0000uy ||
    U8.eq flag 0b0010uy ||
    U8.eq flag max_u8
}

type type_remaining_length =
  (remaining_length: U32.t{U32.v remaining_length <= 268435455 || U32.eq remaining_length max_u32})

type type_error_message_restrict = (error_message: C.String.t{C.String.length error_message <= 30})

// debug tool
assume val print_hex (i:U8.t): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

val slice_byte:
  byte:U8.t
  -> a:U8.t{U8.v a <= 7}
  -> b:U8.t {U8.v b <= 8 && U8.v a < U8.v b}
  -> Stack U8.t
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let slice_byte byte a b =
  let for_mask_temp1 =
    (
      if (U32.eq 0ul (uint8_to_uint32 a)) then
        0b11111111uy
      else if (U32.eq 1ul (uint8_to_uint32 a)) then
        0b01111111uy
      else if (U32.eq 2ul (uint8_to_uint32 a)) then
        0b00111111uy
      else if (U32.eq 3ul (uint8_to_uint32 a)) then
        0b00011111uy
      else if (U32.eq 4ul (uint8_to_uint32 a)) then
        0b00001111uy
      else if (U32.eq 5ul (uint8_to_uint32 a)) then
        0b00000111uy
      else if (U32.eq 6ul (uint8_to_uint32 a)) then
        0b00000011uy
      else
        0b00000001uy
    ) in
  let for_mask_temp2 =
    (
      if (U32.eq 1ul (uint8_to_uint32 b)) then
        0b10000000uy
      else if (U32.eq 2ul (uint8_to_uint32 b)) then
        0b11000000uy
      else if (U32.eq 3ul (uint8_to_uint32 b)) then
        0b11100000uy
      else if (U32.eq 4ul (uint8_to_uint32 b)) then
        0b11110000uy
      else if (U32.eq 5ul (uint8_to_uint32 b)) then
        0b11111000uy
      else if (U32.eq 6ul (uint8_to_uint32 b)) then
        0b11111100uy
      else if (U32.eq 7ul (uint8_to_uint32 b)) then
        0b11111110uy
      else
        0b11111111uy
    ) in
    let mask = U8.logand for_mask_temp1 for_mask_temp2 in
    let r = U8.shift_right (U8.logand byte mask) (U32.sub 8ul (uint8_to_uint32 b)) in
  r

val is_valid_decoding_packet_check: ptr_for_decoding_packets: B.buffer U8.t
  -> bytes_length: (v:U8.t{U8.v v >= 1 && U8.v v <= 4})
  -> Stack (v:U8.t{U8.v v <= 3})
    (requires fun h0 -> B.live h0 ptr_for_decoding_packets /\ B.length ptr_for_decoding_packets = 4)
    (ensures fun h0 r h1 -> true)
let is_valid_decoding_packet_check ptr_for_decoding_packets bytes_length =
  push_frame ();
  let ptr_status: B.buffer (status:U8.t{U8.v status <= 3}) = B.alloca 0uy 1ul in
  let inv h (i: nat) =
    B.live h ptr_status /\
    B.live h ptr_for_decoding_packets
     in
  let body (i: U32.t{ 0 <= U32.v i && U32.v i < 4 }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let ptr_status_v = ptr_status.(0ul) in
    let bytes_length_u32 = uint8_to_uint32(bytes_length) in
      if (U8.eq ptr_status_v 0uy) then
        (
            if (U32.lt i bytes_length_u32) then
                (
                    let decoding_packet = ptr_for_decoding_packets.(i) in
                      // print_u8 decoding_packet;
                      // print_string "<-decoding_packet\n";
                      if (U8.eq bytes_length 1uy) then
                          (
                            if (U8.lt decoding_packet 0uy || U8.gt decoding_packet 127uy) then
                              (
                                // print_string "err1\n";
                                ptr_status.(0ul) <- 1uy
                              )
                          )
                      else
                          (
                            let data_length_minus_one: U32.t = uint8_to_uint32 (U8.sub bytes_length 1uy) in
                            if (U32.eq i data_length_minus_one) then
                              (
                                if (U8.lt decoding_packet 1uy || U8.gt decoding_packet 127uy) then
                                  (
                                    // print_string "err2\n";
                                    ptr_status.(0ul) <- 2uy
                                  )
                              ) else
                                  (
                                    if (U8.lt decoding_packet 128uy || U8.gt decoding_packet max_u8) then
                                      (
                                        // print_string "err3\n";
                                        ptr_status.(0ul) <- 3uy
                                      )
                                  )
                          )
                )

        )
  in
  C.Loops.for 0ul 4ul inv body;
  let r: (status:U8.t{U8.v status <= 3}) = ptr_status.(0ul) in
  pop_frame ();
  r

val most_significant_four_bit_to_zero: i:U8.t -> y:U8.t{U8.v y >= 0 && U8.v y <= 127}
let most_significant_four_bit_to_zero i =
    if (U8.(i >=^ 128uy)) then
      U8.(i -^ 128uy)
    else
      i

val except_most_significant_four_bit_to_zero: i:U8.t -> y:U8.t{U8.v y = 0 || U8.v y = 128}
let except_most_significant_four_bit_to_zero i =
    if (U8.(i <=^ 127uy)) then
      0uy
    else
      128uy

val decodeing_variable_bytes: ptr_for_decoding_packets: B.buffer U8.t
  -> bytes_length:U8.t{U8.v bytes_length >= 1 && U8.v bytes_length <= 4}
  -> Stack (remaining_length:type_remaining_length)
    (requires fun h0 -> B.live h0 ptr_for_decoding_packets  /\ B.length ptr_for_decoding_packets = 4)
    (ensures fun h0 r h1 -> true)
let decodeing_variable_bytes ptr_for_decoding_packets bytes_length =
  push_frame ();
  let ptr_for_decoding_packet: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_for_remaining_length: B.buffer type_remaining_length = B.alloca 0ul 1ul in
  let ptr_status: B.buffer (status:U8.t{U8.v status <= 1}) = B.alloca 1uy 1ul in
  let ptr_temp1 : B.buffer (temp: U32.t{U32.v temp <= 127}) = B.alloca 0ul 1ul in
  let ptr_temp2 : B.buffer (temp: U32.t{U32.v temp <= 16383}) = B.alloca 0ul 1ul in
  let ptr_temp3 : B.buffer (temp: U32.t{U32.v temp <= 2097151}) = B.alloca 0ul 1ul in
  let ptr_temp4 : B.buffer type_remaining_length = B.alloca 0ul 1ul in
  let inv h (i: nat) = B.live h ptr_for_decoding_packets /\
    B.live h ptr_for_decoding_packet /\
    B.live h ptr_for_remaining_length /\
    B.live h ptr_status /\
    B.live h ptr_temp1 /\
    B.live h ptr_temp2 /\
    B.live h ptr_temp3 /\
    B.live h ptr_temp4
     in
  let is_valid_decoding_packet: (v:U8.t{U8.v v <= 3}) = is_valid_decoding_packet_check ptr_for_decoding_packets bytes_length in
  if (is_valid_decoding_packet <> 0uy) then
    (
      pop_frame ();
      max_u32
    )
  else
    (
      let body (i: U32.t{ 0 <= U32.v i && U32.v i <= 3 }): Stack unit
        (requires (fun h -> inv h (U32.v i)))
        (ensures (fun _ _ _ -> true))
      =
        let ptr_status_v = ptr_status.(0ul) in
          if (ptr_status_v = 1uy) then
            (
              let _ = ptr_for_decoding_packet.(0ul) <- ptr_for_decoding_packets.(i) in
              let decoding_packet: U8.t = ptr_for_decoding_packet.(0ul) in

              let b_u8: (x:U8.t{U8.v x >= 0 && U8.v x <= 127}) =
                most_significant_four_bit_to_zero decoding_packet in

              let b_u32: (x:U32.t{U32.v x >= 0 && U32.v x <= 127}) = uint8_to_uint32 b_u8 in
              let b2_u8: (x:U8.t{U8.v x = 0 || U8.v x = 128}) =
                except_most_significant_four_bit_to_zero decoding_packet in

              if (i = 0ul) then
                (
                  ptr_temp1.(0ul) <- U32.(b_u32 *^ 1ul);
                  ptr_for_remaining_length.(0ul) <- ptr_temp1.(0ul)
                )
              else if (i = 1ul) then
                (
                    ptr_temp2.(0ul) <- U32.(ptr_temp1.(0ul) +^ b_u32 *^ 128ul);
                    ptr_for_remaining_length.(0ul) <- ptr_temp2.(0ul)
                )
              else if (i = 2ul) then
                (
                    ptr_temp3.(0ul) <- U32.(ptr_temp2.(0ul) +^ (b_u32 *^ 128ul *^ 128ul));
                    ptr_for_remaining_length.(0ul) <- ptr_temp3.(0ul)
                )
              else
                (
                    ptr_temp4.(0ul) <- U32.(ptr_temp3.(0ul) +^ (b_u32 *^ 128ul *^ 128ul *^ 128ul));
                    ptr_for_remaining_length.(0ul) <- ptr_temp4.(0ul)
                );

              if (b2_u8 = 0uy) then
                ptr_status.(0ul) <- 0uy
            )
      in
      C.Loops.for 0ul 4ul inv body;
      let remaining_length: type_remaining_length =
        ptr_for_remaining_length.(0ul) in
      pop_frame ();
      remaining_length
  )

// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (msg byte) = 25
// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (23byte) = 25
// (1byte) + (1byte) + (23byte) = 25

// (1byte) + (msg len byte 1 or 2 or 3 or 4) + (msg byte) = 100016
// x (1byte) + (msg len byte 1 or 2 or 3 or 4) + (172byte) = 100016
// x (1byte) + (msg len byte 2 or 3 or 4) + (34476byte) = 100016
// x (1byte) + (msg len byte 3 or 4) + (100012byte) = 100016
// (1byte) + (3byte) + (100012byte) = 100016

val get_remaining_length: bytes_length:U8.t{U8.v bytes_length >= 1 && U8.v bytes_length <= 4} -> ptr_for_decoding_packets: B.buffer U8.t -> packet_size:U32.t{1 <= U32.v packet_size}
  -> Stack (remaining_length:type_remaining_length)
  (requires fun h0 -> B.live h0 ptr_for_decoding_packets /\ B.length ptr_for_decoding_packets = 4)
  (ensures fun _ _ _ -> true)
let get_remaining_length bytes_length ptr_for_decoding_packets packet_size =
  push_frame ();
  let fixed_value = U32.(packet_size -^ 1ul) in
  let rr: (remaining_length:type_remaining_length) =
  (
    if (bytes_length = 1uy) then
      (
        let decoding_packet_first: U8.t = ptr_for_decoding_packets.(0ul) in
        let decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
        decoding_packets.(0ul) <- decoding_packet_first;
        let r: (remaining_length:type_remaining_length) = decodeing_variable_bytes decoding_packets bytes_length in
          (
            if (r <> max_u32) then
              (
                if (U32.(1ul +^ r) = fixed_value) then
                  r
                else
                  (
                    // print_string("first bit is not remaining length");
                    max_u32
                  )
              )
            else
              max_u32
          )
      )
      else if (bytes_length = 2uy) then
        (
          let decoding_packet_first: U8.t = ptr_for_decoding_packets.(0ul) in
          let decoding_packet_second: U8.t = ptr_for_decoding_packets.(1ul) in
          let decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
          decoding_packets.(0ul) <- decoding_packet_first;
          decoding_packets.(1ul) <- decoding_packet_second;
          let r: (remaining_length:type_remaining_length) = decodeing_variable_bytes decoding_packets bytes_length in
          (
            if (r <> max_u32) then
              (
                if (U32.(2ul +^ r) = fixed_value) then
                  r
                else
                  (
                    // print_string("first bit is not remaining length");
                    max_u32
                  )
              )
            else
              max_u32
          )
        )
      else if (bytes_length = 3uy) then
        (
          let decoding_packet_first: U8.t = ptr_for_decoding_packets.(0ul) in
          let decoding_packet_second: U8.t = ptr_for_decoding_packets.(1ul) in
          let decoding_packet_third: U8.t = ptr_for_decoding_packets.(2ul) in
          let decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
          decoding_packets.(0ul) <- decoding_packet_first;
          decoding_packets.(1ul) <- decoding_packet_second;
          decoding_packets.(2ul) <- decoding_packet_third;
          let r: (remaining_length:type_remaining_length) = decodeing_variable_bytes decoding_packets bytes_length in
          (
            if (r <> max_u32) then
              (
                if (U32.(3ul +^ r) = fixed_value) then
                  r
                else
                  (
                    // print_string("first bit is not remaining length");
                    max_u32
                  )
              )
            else
              max_u32
          )
        )
      else
        (
          let r: (remaining_length:type_remaining_length) = decodeing_variable_bytes ptr_for_decoding_packets bytes_length in
          (
            if (r <> max_u32) then
              (
                if (U32.(4ul +^ r) = fixed_value) then
                  r
                else
                  (
                    // print_string("first bit is not remaining length");
                    max_u32
                  )
              )
            else
              max_u32
          )
        )
  ) in
  pop_frame ();
  rr

val get_message_type: message_type_bits: U8.t -> type_mqtt_control_packets_restrict
let get_message_type message_type_bits =
  if (U8.eq (is_valid_message_type_check message_type_bits) 0uy) then
    message_type_bits
  else
    max_u8

val get_dup_flag: dup_flag_bits: U8.t -> type_dup_flags
let get_dup_flag dup_flag_bits =
  if (U8.eq (is_valid_dup_flag dup_flag_bits) 0uy) then
    dup_flag_bits
  else
    max_u8

val get_qos_flag: qos_flag_bits: U8.t -> type_qos_flags
let get_qos_flag qos_flag_bits =
  if (U8.eq (is_valid_qos_flag qos_flag_bits) 0uy) then
    qos_flag_bits
  else
    max_u8

val get_retain_flag: retain_flag_bits: U8.t -> type_retain_flags
let get_retain_flag retain_flag_bits =
  if (U8.eq (is_valid_retain_flag retain_flag_bits) 0uy) then
    retain_flag_bits
  else
    max_u8

type struct_flags = {
  flag: type_flag_restrict;
  dup_flag: type_dup_flags_restrict;
  qos_flag: type_qos_flags_restrict;
  retain_flag: type_retain_flags_restrict;
}

type struct_fixed_header_constant = {
  message_type_constant: type_mqtt_control_packets_restrict;
  message_name_constant: type_message_name_restrict;
  flags_constant: struct_flags;
}

type struct_fixed_header = {
  message_type: type_mqtt_control_packets_restrict;
  message_name: type_message_name_restrict;
  flags: struct_flags;
  remaining_length: type_remaining_length;
  error_message: type_error_message_restrict;
}

val is_valid_flag: s:struct_fixed_header_constant -> flag: type_flag_restrict -> bool
let is_valid_flag s flag = U8.eq s.flags_constant.flag flag

val struct_fixed_connect: u:unit -> struct_fixed_header_constant
let struct_fixed_connect u = {
  message_type_constant = define_mqtt_control_packet_CONNECT;
  message_name_constant = define_mqtt_control_packet_CONNECT_label;
  flags_constant = {
    flag = define_flag_CONNECT;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_connack: u:unit -> struct_fixed_header_constant
let struct_fixed_connack u = {
  message_type_constant = define_mqtt_control_packet_CONNACK;
  message_name_constant = define_mqtt_control_packet_CONNACK_label;
  flags_constant = {
    flag = define_flag_CONNACK;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_publish:
  (dup_flag:type_dup_flags_restrict)
  -> (qos_flag:type_qos_flags_restrict)
  -> (retain_flag:type_retain_flags_restrict)
  -> struct_fixed_header_constant
let struct_fixed_publish dup_flag qos_flag retain_flag = {
  message_type_constant = define_mqtt_control_packet_PUBLISH;
  message_name_constant = define_mqtt_control_packet_PUBLISH_label;
  flags_constant = {
    flag = max_u8;
    dup_flag = dup_flag;
    qos_flag = qos_flag;
    retain_flag = retain_flag;
  };
}

val struct_fixed_puback: u:unit -> struct_fixed_header_constant
let struct_fixed_puback u = {
  message_type_constant = define_mqtt_control_packet_PUBACK;
  message_name_constant = define_mqtt_control_packet_PUBACK_label;
  flags_constant = {
    flag = define_flag_PUBACK;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_pubrec: u:unit -> struct_fixed_header_constant
let struct_fixed_pubrec u = {
  message_type_constant = define_mqtt_control_packet_PUBREC;
  message_name_constant = define_mqtt_control_packet_PUBREC_label;
  flags_constant = {
    flag = define_flag_PUBREC;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_pubrel: u:unit -> struct_fixed_header_constant
let struct_fixed_pubrel u = {
  message_type_constant = define_mqtt_control_packet_PUBREL;
  message_name_constant = define_mqtt_control_packet_PUBREL_label;
  flags_constant = {
    flag = define_flag_PUBREL;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_pubcomp: u:unit -> struct_fixed_header_constant
let struct_fixed_pubcomp u = {
  message_type_constant = define_mqtt_control_packet_PUBCOMP;
  message_name_constant = define_mqtt_control_packet_PUBCOMP_label;
  flags_constant = {
    flag = define_flag_PUBCOMP;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_subscribe: u:unit -> struct_fixed_header_constant
let struct_fixed_subscribe u = {
  message_type_constant = define_mqtt_control_packet_SUBSCRIBE;
  message_name_constant = define_mqtt_control_packet_SUBSCRIBE_label;
  flags_constant = {
    flag = define_flag_SUBSCRIBE;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_suback: u:unit -> struct_fixed_header_constant
let struct_fixed_suback u = {
  message_type_constant = define_mqtt_control_packet_SUBACK;
  message_name_constant = define_mqtt_control_packet_SUBACK_label;
  flags_constant = {
    flag = define_flag_SUBACK;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_unsubscribe: u:unit -> struct_fixed_header_constant
let struct_fixed_unsubscribe u = {
  message_type_constant = define_mqtt_control_packet_UNSUBSCRIBE;
  message_name_constant = define_mqtt_control_packet_UNSUBSCRIBE_label;
  flags_constant = {
    flag = define_flag_UNSUBSCRIBE;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_unsuback: u:unit -> struct_fixed_header_constant
let struct_fixed_unsuback u = {
  message_type_constant = define_mqtt_control_packet_UNSUBACK;
  message_name_constant = define_mqtt_control_packet_UNSUBACK_label;
  flags_constant = {
    flag = define_flag_UNSUBACK;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_pingreq: u:unit -> struct_fixed_header_constant
let struct_fixed_pingreq u = {
  message_type_constant = define_mqtt_control_packet_PINGREQ;
  message_name_constant = define_mqtt_control_packet_PINGREQ_label;
  flags_constant = {
    flag = define_flag_PINGREQ;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_pingresp: u:unit -> struct_fixed_header_constant
let struct_fixed_pingresp u = {
  message_type_constant = define_mqtt_control_packet_PINGRESP;
  message_name_constant = define_mqtt_control_packet_PINGRESP_label;
  flags_constant = {
    flag = define_flag_PINGRESP;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_disconnect: u:unit -> struct_fixed_header_constant
let struct_fixed_disconnect u = {
  message_type_constant = define_mqtt_control_packet_DISCONNECT;
  message_name_constant = define_mqtt_control_packet_DISCONNECT_label;
  flags_constant = {
    flag = define_flag_DISCONNECT;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val struct_fixed_auth: u:unit -> struct_fixed_header_constant
let struct_fixed_auth u = {
  message_type_constant = define_mqtt_control_packet_AUTH;
  message_name_constant = define_mqtt_control_packet_AUTH_label;
  flags_constant = {
    flag = define_flag_AUTH;
    dup_flag = max_u8;
    qos_flag = max_u8;
    retain_flag = max_u8;
  };
}

val bytes_loop: request: B.buffer U8.t -> packet_size: U32.t -> Stack struct_fixed_header
  (requires fun h0 -> B.live h0 request /\ B.length request = U32.v packet_size )
  (ensures fun _ _ _ -> true)
let bytes_loop request packet_size =
  push_frame ();
  let ptr_fixed_header_first_one_byte: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_status: B.buffer (status:U8.t{U8.v status <= 1}) = B.alloca 1uy 1ul in
  let ptr_for_decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
  let ptr_remaining_length: B.buffer type_remaining_length =
   B.alloca 0ul 1ul in
  let inv h (i: nat) =
    B.live h ptr_fixed_header_first_one_byte /\
    B.live h request /\
    B.live h ptr_for_decoding_packets /\
    B.live h ptr_status /\
    B.live h ptr_remaining_length
    in
  let body (i: U32.t{ 0 <= U32.v i && U32.v i < U32.v packet_size }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let one_byte : U8.t = request.(i) in
        let ptr_status_v: (status:U8.t{U8.v status <= 1}) = ptr_status.(0ul) in
      if (i = 0ul) then
        (
          ptr_fixed_header_first_one_byte.(0ul) <- one_byte
        )
      else if (i = 1ul) then
        (
          ptr_for_decoding_packets.(0ul) <- one_byte;
          let r: (remaining_length:type_remaining_length) =
            get_remaining_length 1uy ptr_for_decoding_packets packet_size in
          if (r <> max_u32) then (
            ptr_status.(0ul) <- 0uy;
            ptr_remaining_length.(0ul) <- r
          )
        )
      else if (i = 2ul) then
        (
          if (ptr_status_v = 1uy) then
            (
              ptr_for_decoding_packets.(1ul) <- one_byte;
              let r: (remaining_length:type_remaining_length) =
                get_remaining_length 2uy ptr_for_decoding_packets packet_size in
              if (r <> max_u32) then (
                ptr_status.(0ul) <- 0uy;
                ptr_remaining_length.(0ul) <- r
              )
            )
        )
      else if (i = 3ul) then
        (
          if (ptr_status_v = 1uy) then
            (
              ptr_for_decoding_packets.(2ul) <- one_byte;
              let r: (remaining_length:type_remaining_length)
                = get_remaining_length 3uy ptr_for_decoding_packets packet_size in
              if (r <> max_u32) then (
                ptr_status.(0ul) <- 0uy;
                ptr_remaining_length.(0ul) <- r
              )
            )
        )
      else if (i = 4ul) then
        (
          if (ptr_status_v = 1uy) then
            (
              ptr_for_decoding_packets.(3ul) <- one_byte;
              let r: (remaining_length:type_remaining_length)
                = get_remaining_length 4uy ptr_for_decoding_packets packet_size in
              if (r <> max_u32) then (
                ptr_status.(0ul) <- 0uy;
                ptr_remaining_length.(0ul) <- r
              )
            )
        )
  in
  C.Loops.for 0ul packet_size inv body;
  let status: (s:U8.t{U8.v s <= 1}) = ptr_status.(0ul) in
  let fixed_header_first_one_byte = ptr_fixed_header_first_one_byte.(0ul) in
  let message_type_bits: U8.t = slice_byte fixed_header_first_one_byte 0uy 4uy in
  let message_type: type_mqtt_control_packets_restrict = get_message_type message_type_bits in
  let remaining_length: type_remaining_length
    = ptr_remaining_length.(0ul) in
  if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
    (
      let dup_flag: type_dup_flags_restrict =
      (
        if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
            let dup_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 4uy 5uy in
            get_dup_flag dup_flag_bits
        else
          max_u8
        ) in
      let qos_flag: type_qos_flags_restrict =
      (
        if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
            let qos_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 5uy 7uy in
            get_qos_flag qos_flag_bits
        else
          max_u8
        ) in
      let retain_flag: type_retain_flags_restrict =
      (
        if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
          let retain_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 7uy 8uy in
            get_retain_flag retain_flag_bits
        else
          max_u8
      ) in
      let have_error: bool =
          (U8.eq status 1uy) ||
          (U8.eq message_type max_u8) ||
          (U8.eq dup_flag max_u8) ||
          (U8.eq qos_flag max_u8) ||
          (U8.eq retain_flag max_u8) in
      let error_message: type_error_message_restrict =
        (
          if (have_error) then (
            if (U8.eq status 1uy) then
              !$"remaining_length is invalid."
            else if (U8.eq message_type max_u8) then
              !$"message_type is invalid."
            else if (U8.eq dup_flag max_u8) then
              !$"dup_flag is invalid."
            else if (U8.eq qos_flag max_u8) then
              !$"qos_flag is invalid."
            else if (U8.eq retain_flag max_u8) then
              !$"retain_flag is invalid."
            else
              !$"unexpected error."
          ) else
            !$""
        ) in
      pop_frame ();
      if (have_error) then
        {
          message_type = max_u8;
          message_name = !$"";
          flags = {
            flag = max_u8;
            dup_flag = max_u8;
            qos_flag = max_u8;
            retain_flag = max_u8;
          };
          remaining_length = 0ul;
          error_message = error_message;
        }
      else
        let data: struct_fixed_header_constant =
          struct_fixed_publish dup_flag qos_flag retain_flag in
          {
            message_type = data.message_type_constant;
            message_name = data.message_name_constant;
            flags = {
              flag = data.flags_constant.flag;
              dup_flag = data.flags_constant.dup_flag;
              qos_flag = data.flags_constant.qos_flag;
              retain_flag = data.flags_constant.retain_flag;
            };
            remaining_length = remaining_length;
            error_message = !$"";
          }
    )
  else
    (
      let flag: type_flag_restrict =
        let v = slice_byte fixed_header_first_one_byte 4uy 8uy in
          (
            if (v <> 0b0000uy && v <> 0b0010uy && v <> max_u8) then
              max_u8
            else
              v
          ) in
      let data: struct_fixed_header_constant =
        if (U8.eq message_type define_mqtt_control_packet_CONNECT) then
          struct_fixed_connect ()
        else if (U8.eq message_type define_mqtt_control_packet_CONNACK) then
          struct_fixed_connack ()
        else if (U8.eq message_type define_mqtt_control_packet_PUBACK) then
          struct_fixed_puback ()
        else if (U8.eq message_type define_mqtt_control_packet_PUBREC) then
          struct_fixed_pubrec ()
        else if (U8.eq message_type define_mqtt_control_packet_PUBREL) then
          struct_fixed_pubrel ()
        else if (U8.eq message_type define_mqtt_control_packet_PUBCOMP) then
          struct_fixed_pubcomp ()
        else if (U8.eq message_type define_mqtt_control_packet_SUBSCRIBE) then
          struct_fixed_subscribe ()
        else if (U8.eq message_type define_mqtt_control_packet_SUBACK) then
          struct_fixed_suback ()
        else if (U8.eq message_type define_mqtt_control_packet_UNSUBSCRIBE) then
          struct_fixed_unsubscribe ()
        else if (U8.eq message_type define_mqtt_control_packet_UNSUBACK) then
          struct_fixed_unsuback ()
        else if (U8.eq message_type define_mqtt_control_packet_PINGREQ) then
          struct_fixed_pingreq ()
        else if (U8.eq message_type define_mqtt_control_packet_PINGRESP) then
          struct_fixed_pingresp ()
        else if (U8.eq message_type define_mqtt_control_packet_DISCONNECT) then
          struct_fixed_disconnect ()
        else
          struct_fixed_auth () in
      let have_error: bool =
        (U8.eq status 1uy) ||
        (U8.eq message_type max_u8) ||
        (is_valid_flag data flag = false) in
        pop_frame ();
        if (have_error) then
          (
            {
              message_type = max_u8;
              message_name = !$"";
              flags = {
                flag = max_u8;
                dup_flag = max_u8;
                qos_flag = max_u8;
                retain_flag = max_u8;
              };
              remaining_length = 0ul;
              error_message =
                if (U8.eq status 1uy) then
                  !$"remaining_length is invalid."
                else if (U8.eq message_type max_u8) then
                  !$"message_type is invalid."
                else if (is_valid_flag data flag = false) then
                  !$"flag is invalid."
                else
                  !$"unexpected error."
              }
            )
        else
          {
            message_type = data.message_type_constant;
            message_name = data.message_name_constant;
            flags = {
              flag = data.flags_constant.flag;
              dup_flag = data.flags_constant.dup_flag;
              qos_flag = data.flags_constant.qos_flag;
              retain_flag = data.flags_constant.retain_flag;
            };
            remaining_length = remaining_length;
            error_message = !$"";
          }
    )

val parse (request: B.buffer U8.t) (packet_size: U32.t):
  Stack struct_fixed_header
    (requires (fun h ->
      B.live h request /\
      B.length request <= 268435460 /\
      U32.v packet_size <= 268435460 /\
      B.length request = U32.v packet_size))
    (ensures (fun h0 _ h1 ->
      B.live h1 request))
let parse request packet_size =
    push_frame ();
    let data: struct_fixed_header = bytes_loop request packet_size in
    pop_frame ();
    data