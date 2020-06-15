module Common

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Int.Cast
open LowStar.Printf
open C.String


open Const

val most_significant_four_bit_to_zero: i:U8.t -> y:U8.t{U8.v y >= 0 && U8.v y <= 127}
let most_significant_four_bit_to_zero i =
    if (U8.(i >=^ 128uy)) then
      U8.(i -^ 128uy)
    else
      i

val decodeing_variable_bytes: ptr_for_decoding_packets: B.buffer U8.t
  -> bytes_length:U8.t{U8.v bytes_length >= 1 && U8.v bytes_length <= 4}
  -> Stack (remaining_length:type_remaining_length)
    (requires fun h0 -> B.live h0 ptr_for_decoding_packets  /\ B.length ptr_for_decoding_packets = 4)
    (ensures fun h0 r h1 -> true)
let decodeing_variable_bytes ptr_for_decoding_packets bytes_length =
  push_frame ();
  let ptr_for_decoding_packet: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_for_remaining_length: B.buffer type_remaining_length = B.alloca 0ul 1ul in
  let ptr_temp1 : B.buffer (temp: U32.t{U32.v temp <= 127}) = B.alloca 0ul 1ul in
  let ptr_temp2 : B.buffer (temp: U32.t{U32.v temp <= 16383}) = B.alloca 0ul 1ul in
  let ptr_temp3 : B.buffer (temp: U32.t{U32.v temp <= 2097151}) = B.alloca 0ul 1ul in
  let ptr_temp4 : B.buffer type_remaining_length = B.alloca 0ul 1ul in
  let inv h (i: nat) = B.live h ptr_for_decoding_packets /\
    B.live h ptr_for_decoding_packet /\
    B.live h ptr_for_remaining_length /\
    B.live h ptr_temp1 /\
    B.live h ptr_temp2 /\
    B.live h ptr_temp3 /\
    B.live h ptr_temp4 in
  let body (i: U32.t{ 0 <= U32.v i && U32.v i <= 3 }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
    let decoding_packet: U8.t = ptr_for_decoding_packets.(i) in
    let b_u8: (x:U8.t{U8.v x >= 0 && U8.v x <= 127}) =
      most_significant_four_bit_to_zero decoding_packet in
    let b_u32: (x:U32.t{U32.v x >= 0 && U32.v x <= 127}) = uint8_to_uint32 b_u8 in
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
      )
  in
  C.Loops.for 0ul 4ul inv body;
  let remaining_length: type_remaining_length =
    ptr_for_remaining_length.(0ul) in
  pop_frame ();
  remaining_length


val get_variable_byte: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> now_index:U32.t
  -> Stack (variable_length: struct_variable_length)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let get_variable_byte packet_data packet_size now_index =
  push_frame ();
  let ptr_for_decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
  let ptr_remaining_length: B.buffer type_remaining_length =
   B.alloca 0ul 1ul in
  let ptr_byte_length: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_next_start_index: B.buffer U32.t = B.alloca 0ul 1ul in
  let loop_last: U32.t = 
    (
      if U32.( (packet_size -^ now_index ) <^ 4ul) then
        packet_size 
      else
        U32.add now_index 4ul
    ) in
  let inv h (i: nat) = B.live h packet_data /\ 
  B.live h ptr_for_decoding_packets /\
  B.live h ptr_remaining_length /\
  B.live h ptr_byte_length in
  let body (i): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
      if (ptr_byte_length.(0ul) = 0uy) then
        (
          let j = U32.sub i now_index in
          ptr_for_decoding_packets.(j) <- packet_data.(i);
          let is_end_byte: bool =
            (
              if (U32.eq i 1ul && U8.lte packet_data.(i) 0x7Fuy) ||
                (U32.gte i 2ul && U8.gte packet_data.(i) 0x01uy && U8.lte packet_data.(i) 0x7Fuy)
                then
                true
              else
                false
            ) in

            if (is_end_byte) then
              (
                let bytes_length_u8: U8.t = uint32_to_uint8(U32.add j 1ul) in
                let untrust_remaining_length: type_remaining_length =
                  decodeing_variable_bytes ptr_for_decoding_packets bytes_length_u8 in
                let byte_length: U32.t = U32.add untrust_remaining_length i in
                let valid_remaining_length: bool = 
                  U32.eq (U32.sub packet_size 1ul) (U32.add untrust_remaining_length i) in
                if valid_remaining_length then (
                  ptr_remaining_length.(0ul) <- untrust_remaining_length;
                  ptr_byte_length.(0ul) <- bytes_length_u8;
                  ptr_next_start_index.(0ul) <- U32.add i 1ul
                )           
              )
        )
  in
  C.Loops.for now_index loop_last inv body;
  let remaining_length = ptr_remaining_length.(0ul) in
  let byte_length = ptr_byte_length.(0ul) in
  let next_start_index = ptr_next_start_index.(0ul) in
  pop_frame ();

  if (byte_length = 0uy) then
    {
      have_error = true;
      variable_length_value = max_u32;
      next_start_index = max_u32;
    }
  else
    {
      have_error = false;
      variable_length_value = remaining_length;
      next_start_index = next_start_index;
    }

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

val replace_utf8_encoded: data: (B.buffer U8.t) 
  -> data_size: U32.t 
  -> Stack (r: B.buffer U8.t)
    (requires fun h0 -> B.live h0 data)
    (ensures fun h0 r h1 -> true)
let replace_utf8_encoded data data_size =
  push_frame ();
  let ptr_search_counter: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_return_data: B.buffer U8.t = B.alloca 0uy data_size in
  let ptr_counter: B.buffer U32.t = B.alloca 0ul data_size in
  let inv h (i: nat) = B.live h data /\ 
  B.live h ptr_search_counter in
  let body (i): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
    (
      let one_byte: U8.t = data.(i) in
      let search_count = ptr_search_counter.(0ul) in
      ptr_return_data.(U32.sub i ptr_counter.(0ul)) <- one_byte;
      if (U8.eq search_count 0uy && U8.eq one_byte 0xEFuy) then
        (
          ptr_search_counter.(0ul) <- 1uy
        )
      else if (U8.eq search_count 1uy &&  U8.eq one_byte 0xBBuy) then
        (
          ptr_search_counter.(0ul) <- 2uy
        )
      else if (U8.eq search_count 2uy &&  U8.eq one_byte 0xBFuy) then
        (
          // ptr_search_counter.(0ul) <- 3uy
          ptr_return_data.(U32.sub i 2ul) <- 0xFEuy;
          ptr_return_data.(U32.sub i 1ul) <- 0xFFuy;
          ptr_return_data.(i) <- 0x00uy;
          ptr_counter.(0ul) <- U32.add ptr_counter.(0ul) 1ul;
          ptr_search_counter.(0ul) <- 0uy
        )
      else
        (
          ptr_search_counter.(0ul) <- 0uy
        )
    )
  in
  C.Loops.for 0ul data_size inv body;
  let return_data: B.buffer U8.t = ptr_return_data in
  pop_frame ();
  return_data