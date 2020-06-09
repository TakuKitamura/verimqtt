module Common

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Int.Cast
open C.String


open Const

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
    let ptr_status_v: (status:U8.t{U8.v status <= 3}) = ptr_status.(0ul) in
    let bytes_length_u32: U32.t = uint8_to_uint32(bytes_length) in
      if (U8.eq ptr_status_v 0uy) then
        (
          if (U32.lt i bytes_length_u32) then
            (
              let decoding_packet: U8.t = ptr_for_decoding_packets.(i) in
                if (U8.eq bytes_length 1uy) then
                  (
                    if (U8.lt decoding_packet 0uy || U8.gt decoding_packet 127uy) then
                      (
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
                            ptr_status.(0ul) <- 2uy
                          )
                      ) else
                        (
                          if (U8.lt decoding_packet 128uy || U8.gt decoding_packet max_u8) then
                            (
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
        let ptr_status_v: (status:U8.t{U8.v status <= 1}) = ptr_status.(0ul) in
          if (ptr_status_v = 1uy) then
            (
              let decoding_packet: U8.t = ptr_for_decoding_packets.(i) in

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

val get_remaining_length: bytes_length:U8.t{U8.v bytes_length >= 1 && U8.v bytes_length <= 4} -> ptr_for_decoding_packets: B.buffer U8.t -> packet_size: type_packet_size
  -> Stack (remaining_length:type_remaining_length)
  (requires fun h0 -> B.live h0 ptr_for_decoding_packets /\ B.length ptr_for_decoding_packets = 4)
  (ensures fun _ _ _ -> true)
let get_remaining_length bytes_length ptr_for_decoding_packets packet_size =
  let fixed_value: U32.t = U32.(packet_size -^ 1ul) in
  let bytes_length_u32: U32.t = uint8_to_uint32(bytes_length) in
  let r: type_remaining_length =
    let untrust_r: type_remaining_length =
      decodeing_variable_bytes ptr_for_decoding_packets bytes_length in
    (
      if (untrust_r <> max_u32) then
        (
          if (U32.(bytes_length_u32 +^ untrust_r) = fixed_value) then
            untrust_r
          else
            max_u32
        )
      else
        max_u32
    ) in r

val get_message_type: message_type_bits: U8.t -> type_mqtt_control_packets_restrict
let get_message_type message_type_bits =
  if (U8.lt message_type_bits 1uy || U8.gt message_type_bits 15uy) then
    max_u8
  else
    message_type_bits

val is_valid_flag: s:struct_fixed_header_constant -> flag: type_flag_restrict -> bool
let is_valid_flag s flag = U8.eq s.flags_constant.flag flag

val get_struct_fixed_header_constant_except_publish :
  (message_type: type_mqtt_control_packets_restrict)
  -> struct_fixed_header_constant
let get_struct_fixed_header_constant_except_publish message_type =
  if (U8.eq message_type define_mqtt_control_packet_CONNECT) then
    {
      message_type_constant = define_mqtt_control_packet_CONNECT;
      message_name_constant = define_mqtt_control_packet_CONNECT_label;
      flags_constant = {
        flag = define_flag_CONNECT;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_CONNACK) then
      {
        message_type_constant = define_mqtt_control_packet_CONNACK;
        message_name_constant = define_mqtt_control_packet_CONNACK_label;
        flags_constant = {
          flag = define_flag_CONNACK;
          dup_flag = max_u8;
          qos_flag = max_u8;
          retain_flag = max_u8;
        };
      }
  else if (U8.eq message_type define_mqtt_control_packet_PUBACK) then
    {
      message_type_constant = define_mqtt_control_packet_PUBACK;
      message_name_constant = define_mqtt_control_packet_PUBACK_label;
      flags_constant = {
        flag = define_flag_PUBACK;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_PUBREC) then
    {
      message_type_constant = define_mqtt_control_packet_PUBREC;
      message_name_constant = define_mqtt_control_packet_PUBREC_label;
      flags_constant = {
        flag = define_flag_PUBREC;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_PUBREL) then
    {
      message_type_constant = define_mqtt_control_packet_PUBREL;
      message_name_constant = define_mqtt_control_packet_PUBREL_label;
      flags_constant = {
        flag = define_flag_PUBREL;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_PUBCOMP) then
    {
      message_type_constant = define_mqtt_control_packet_PUBCOMP;
      message_name_constant = define_mqtt_control_packet_PUBCOMP_label;
      flags_constant = {
        flag = define_flag_PUBCOMP;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_SUBSCRIBE) then
    {
      message_type_constant = define_mqtt_control_packet_SUBSCRIBE;
      message_name_constant = define_mqtt_control_packet_SUBSCRIBE_label;
      flags_constant = {
        flag = define_flag_SUBSCRIBE;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_SUBACK) then
    {
      message_type_constant = define_mqtt_control_packet_SUBACK;
      message_name_constant = define_mqtt_control_packet_SUBACK_label;
      flags_constant = {
        flag = define_flag_SUBACK;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_UNSUBSCRIBE) then
    {
      message_type_constant = define_mqtt_control_packet_UNSUBSCRIBE;
      message_name_constant = define_mqtt_control_packet_UNSUBSCRIBE_label;
      flags_constant = {
        flag = define_flag_UNSUBSCRIBE;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_UNSUBACK) then
    {
      message_type_constant = define_mqtt_control_packet_UNSUBACK;
      message_name_constant = define_mqtt_control_packet_UNSUBACK_label;
      flags_constant = {
        flag = define_flag_UNSUBACK;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_PINGREQ) then
    {
      message_type_constant = define_mqtt_control_packet_PINGREQ;
      message_name_constant = define_mqtt_control_packet_PINGREQ_label;
      flags_constant = {
        flag = define_flag_PINGREQ;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_PINGRESP) then
    {
      message_type_constant = define_mqtt_control_packet_PINGRESP;
      message_name_constant = define_mqtt_control_packet_PINGRESP_label;
      flags_constant = {
        flag = define_flag_PINGRESP;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else if (U8.eq message_type define_mqtt_control_packet_DISCONNECT) then
    {
      message_type_constant = define_mqtt_control_packet_DISCONNECT;
      message_name_constant = define_mqtt_control_packet_DISCONNECT_label;
      flags_constant = {
        flag = define_flag_DISCONNECT;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }
  else
    {
      message_type_constant = define_mqtt_control_packet_AUTH;
      message_name_constant = define_mqtt_control_packet_AUTH_label;
      flags_constant = {
        flag = define_flag_AUTH;
        dup_flag = max_u8;
        qos_flag = max_u8;
        retain_flag = max_u8;
      };
    }

val error_struct_fixed_header:
  (error_struct: struct_error_struct)
  -> struct_fixed_header
let error_struct_fixed_header error_struct = {
    message_type = max_u8;
    message_name = !$"";
    flags = {
      flag = max_u8;
      dup_flag = max_u8;
      qos_flag = max_u8;
      retain_flag = max_u8;
    };
    remaining_length = max_u32;
    connect = {
      protocol_name = !$"";
      protocol_version = max_u8;
      flags = {
        connect_flag = max_u8;
        user_name = max_u8;
        password = max_u8;
        will_retain = max_u8;
        will_qos = max_u8;
        will_flag = max_u8;
        clean_start = max_u8;
      };
      keep_alive = max_u32;
      connect_topic_length = max_u32;
      connect_property = {
        connect_property_id = max_u8;
        connect_property_name = !$"";
      }
    };
    publish = {
      topic_length = max_u32;
      topic_name = !$"";
      property_length = max_u32;
      payload = !$"";
    };
    disconnect = {
      disconnect_reason_code = max_u8;
      disconnect_reason_code_name = !$"";
    };
    error = error_struct;
  }

let zero_terminated_buffer_u8 (h: HS.mem) (b: B.buffer U8.t) =
  let s = B.as_seq h b in
  B.length b > 0 /\
  B.length b <= FStar.UInt.max_int 32 /\
  U8.v (Seq.index s (B.length b - 1)) = 0

val slice_byte:
  byte:U8.t
  -> a:U8.t{U8.v a <= 7}
  -> b:U8.t {U8.v b <= 8 && U8.v a < U8.v b} -> U8.t
let slice_byte byte a b =
  let for_mask_temp1: U8.t =
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
  let for_mask_temp2: U8.t =
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
    let mask: U8.t = U8.logand for_mask_temp1 for_mask_temp2 in
    let r: U8.t = U8.shift_right (U8.logand byte mask) (U32.sub 8ul (uint8_to_uint32 b)) in
  r


val get_flag: (message_type: type_mqtt_control_packets_restrict)
  -> (fixed_header_first_one_byte: U8.t)
  -> type_flag_restrict
let get_flag message_type fixed_header_first_one_byte =
  let v: U8.t = slice_byte fixed_header_first_one_byte 4uy 8uy in
      if (U8.eq message_type define_mqtt_control_packet_PUBREL ||
        U8.eq message_type define_mqtt_control_packet_SUBSCRIBE ||
        U8.eq message_type define_mqtt_control_packet_UNSUBSCRIBE) then
        (
          if (v <> 0b0010uy) then
            max_u8
          else
            v
        )
      else
        (
          if (v <> 0b0000uy) then
            max_u8
          else
            v
        )

