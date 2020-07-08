module Common

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Int.Cast
open LowStar.Printf
open C.String


open Const
open FFI
open Debug_FFI

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
              if (U32.eq j 0ul && U8.lte packet_data.(i) 0x7Fuy) ||
                (U32.gte j 1ul && U8.gte packet_data.(i) 0x01uy && U8.lte packet_data.(i) 0x7Fuy)
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
                let byte_length: U32.t = U32.add j 1ul in
                let valid_remaining_length: bool = 
                  (
                    if (U32.eq now_index 1ul) then
                      U32.eq (U32.sub packet_size 1ul) (U32.add untrust_remaining_length i)
                    else 
                      true
                  ) in
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
    remaining_length = 0ul;
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
      connect_topic_length = 0ul;
      connect_property = {
        connect_property_id = max_u8;
        connect_property_name = !$"";
      }
    };
    publish = {
      topic_length = 0ul;
      topic_name = !$"";
      property_length = 0ul;
      payload = !$"";
      payload_length = 0ul;
      property_id = max_u8;
    };
    disconnect = {
      disconnect_reason_code = max_u8;
      disconnect_reason_code_name = !$"";
    };
    property = property_struct_base;
    error = error_struct;
  }

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
  -> Stack (r: struct_replace_utf8_encoded)
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
  let bom_data: B.buffer U8.t = ptr_return_data in
  let bom_count: U32.t = ptr_counter.(0ul) in
  pop_frame ();
  let replace_utf8_encoded: struct_replace_utf8_encoded = {
    replace_bom = bom_data;
    bom_count = bom_count;
  } in replace_utf8_encoded

val share_common_data_check: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> Stack (share_common_data_check: struct_share_common_data_check)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let share_common_data_check packet_data packet_size =
  let first_one_byte: U8.t = packet_data.(0ul) in
  let message_type_bits: U8.t = slice_byte first_one_byte 0uy 4uy in
  let message_type: type_mqtt_control_packets_restrict = get_message_type message_type_bits in

  let variable_length: struct_variable_length = get_variable_byte packet_data packet_size 1ul in
  let remaining_length: type_remaining_length = variable_length.variable_length_value in

  let next_start_index: U32.t = variable_length.next_start_index in
  let is_share_error: bool = (variable_length.have_error) || (U8.eq message_type max_u8) in
  if (is_share_error) then
    (
      let error_struct: struct_error_struct =
        (
          if (variable_length.have_error) then
            {
              code = define_error_remaining_length_invalid_code;
              message = define_error_remaining_length_invalid;
            }
          else // if (U8.eq message_type max_u8) then
            {
              code = define_error_message_type_invalid_code;
              message = define_error_message_type_invalid;
            }
        ) in 
        let error = error_struct_fixed_header error_struct in
        let share_common_data_check: struct_share_common_data_check =
        {
          share_common_data_have_error = is_share_error;
          share_common_data_error = error;
          share_common_data = {
            common_packet_data = packet_data;
            common_packet_size = packet_size;
            common_message_type = max_u8;
            common_remaining_length = max_u32;
            common_next_start_index = max_u32;
            common_first_one_byte = max_u8;
          };
        } in share_common_data_check
    )
  else
    (
     let error_struct: struct_error_struct =
        (
          {
            code = define_no_error_code;
            message = !$"";
          }
        ) in 
        let no_error = error_struct_fixed_header error_struct in
        let share_common_data: struct_share_common_data =
          {
            common_packet_data = packet_data;
            common_packet_size = packet_size;
            common_message_type = message_type;
            common_remaining_length = remaining_length;
            common_next_start_index = next_start_index;
            common_first_one_byte = first_one_byte;
          } in
        let share_common_data_check: struct_share_common_data_check =
        {
          share_common_data_have_error = is_share_error;
          share_common_data_error = no_error;
          share_common_data = share_common_data;
        } in share_common_data_check
    )

// 1: Byte
// 2: Two Byte Integer
// 3: Four Byte Integer
// 4: UTF-8 Encoded String
// 5: Variable Byte Integer
// 6: Binary Data
// 7: UTF-8 String Pair
val get_property_type_id: property_id: (U8.t)
  -> property_type_id: (U8.t)
let get_property_type_id property_id =
  if (property_id = 0x01uy || property_id = 0x17uy || property_id = 0x19uy || property_id = 0x24uy || property_id = 0x25uy || property_id = 0x28uy || property_id = 0x29uy || property_id = 0x2Auy) then
    0x01uy // Byte
  else if (property_id = 0x13uy || property_id = 0x21uy || property_id = 0x22uy || property_id = 0x23uy) then
    0x02uy // Two Byte Integer
  else if (property_id = 0x02uy || property_id = 0x11uy || property_id = 0x18uy || property_id = 0x27uy) then
    0x03uy // Four Byte Integer
  else if (property_id = 0x03uy || property_id = 0x08uy || property_id = 0x12uy || property_id = 0x15uy || property_id = 0x1Auy || property_id = 0x1Cuy || property_id = 0x1Fuy) then
    0x04uy // UTF-8 Encoded String
  else if (property_id = 0x0Buy) then
    0x05uy // Variable Byte Integer
  else if (property_id = 0x09uy || property_id = 0x16uy) then
    0x06uy // Binary Data
  else if (property_id = 0x26uy) then
    0x07uy // UTF-8 String Pair
  else
    max_u8

val get_two_byte_integer_u8_to_u32: msb_u8: (U8.t)
  -> lsb_u8: (U8.t)
  -> two_byte_integer: (U32.t)
let get_two_byte_integer_u8_to_u32 msb_u8 lsb_u8 =
  let msb_u32: U32.t = uint8_to_uint32 msb_u8 in
  let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
  let two_byte_integer: U32.t =
    U32.logor (U32.shift_left msb_u32 8ul) lsb_u32
  in two_byte_integer 

val get_two_byte_integer_u8_to_u16: msb_u8: (U8.t)
  -> lsb_u8: (U8.t)
  -> two_byte_integer: (U16.t)
let get_two_byte_integer_u8_to_u16 msb_u8 lsb_u8 =
  let msb_u16: U16.t = uint8_to_uint16 msb_u8 in
  let lsb_u16: U16.t = uint8_to_uint16 lsb_u8 in
  let two_byte_integer: U16.t =
    U16.logor (U16.shift_left msb_u16 8ul) lsb_u16
  in two_byte_integer 

val get_four_byte_integer: 
  mmsb_u8: (U8.t)
  -> msb_u8: (U8.t)
  -> lsb_u8: (U8.t)
  -> llsb_u8: (U8.t)
  -> four_byte_integer: (U32.t)
let get_four_byte_integer mmsb_u8 msb_u8 lsb_u8 llsb_u8 =
  let mmsb_u32: U32.t = uint8_to_uint32 mmsb_u8 in
  let msb_u32: U32.t = uint8_to_uint32 msb_u8 in
  let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
  let llsb_u32: U32.t = uint8_to_uint32 llsb_u8 in
  let four_byte_integer: U32.t =
    U32.logor 
      (U32.logor (U32.shift_left mmsb_u32 24ul) (U32.shift_left msb_u32 16ul))
      (U32.logor (U32.shift_left lsb_u32 8ul) llsb_u32) 
  in four_byte_integer 
   
// TODO: Payloadはnull終端である必要はないので関数呼び出し側は注意する
val get_payload: packet_data: (B.buffer U8.t) 
  -> payload_start_index: U32.t
  -> packet_end_index: U32.t
  -> Stack (payload: struct_payload)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let get_payload packet_data payload_start_index payload_end_index =
  let payload_length: U32.t = U32.(payload_end_index -^ payload_start_index +^ 1ul) in
  let payload_offset: type_payload_offset = payload_start_index in
  let ptr_payload_u8: B.buffer U8.t = B.offset packet_data payload_offset in

  let payload :struct_payload = {
    is_valid_payload = true;
    payload = ptr_payload_u8;
    payload_length = payload_length;
  } in payload

val parse_property_two_byte_integer: packet_data: (B.buffer U8.t) 
  -> property_start_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_two_byte_integer packet_data property_start_index =
  push_frame ();
  let msb_u8: U8.t = packet_data.(U32.add property_start_index 1ul) in
  let lsb_u8: U8.t = packet_data.(U32.add property_start_index 2ul) in
  pop_frame ();
  let two_byte_integer: U32.t = get_two_byte_integer_u8_to_u32 msb_u8 lsb_u8 in
  let two_byte_integer_struct: struct_two_byte_integer = {
    two_byte_integer_value = uint32_to_uint16 two_byte_integer;
  } in
  let b: struct_property_type = property_struct_type_base in
  let property_struct_type_base: struct_property_type = {
    one_byte_integer_struct = {
      one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
    };
    two_byte_integer_struct = two_byte_integer_struct;
    four_byte_integer_struct = {
      four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
    };
    utf8_encoded_string_struct = {
      utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
      utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
      utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
    };
    variable_byte_integer_struct = {
      variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
    };
    binary_data_struct = {
      binary_length = b.binary_data_struct.binary_length;
      binary_value = b.binary_data_struct.binary_value;
    };
    utf8_string_pair_struct = {
      utf8_string_pair_key = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
      };
      utf8_string_pair_value = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
      };
    };
    property_type_error_code = 0uy;
  } in property_struct_type_base
  
val parse_property_four_byte_integer: packet_data: (B.buffer U8.t) 
  -> property_start_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_four_byte_integer packet_data property_start_index =
  push_frame ();
  let mmsb_u8: U8.t = packet_data.(U32.add property_start_index 1ul) in
  let msb_u8: U8.t = packet_data.(U32.add property_start_index 2ul) in
  let lsb_u8: U8.t = packet_data.(U32.add property_start_index 3ul) in
  let llsb_u8: U8.t = packet_data.(U32.add property_start_index 4ul) in
  pop_frame ();
  let four_byte_integer: U32.t = get_four_byte_integer mmsb_u8 msb_u8 lsb_u8 llsb_u8 in
  let four_byte_integer_struct: struct_four_byte_integer = {
    four_byte_integer_value = four_byte_integer;
  } in
  let b: struct_property_type = property_struct_type_base in
  let property_struct_type_base: struct_property_type = {
    one_byte_integer_struct = {
      one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
    };
    two_byte_integer_struct = {
      two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
    };
    four_byte_integer_struct = four_byte_integer_struct;
    utf8_encoded_string_struct = {
      utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
      utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
      utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
    };
    variable_byte_integer_struct = {
      variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
    };
    binary_data_struct = {
      binary_length = b.binary_data_struct.binary_length;
      binary_value = b.binary_data_struct.binary_value;
    };
    utf8_string_pair_struct = {
      utf8_string_pair_key = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
      };
      utf8_string_pair_value = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
      };
    };
    property_type_error_code = 0uy;
  } in property_struct_type_base

val parse_property_one_byte_integer: packet_data: (B.buffer U8.t) 
  -> property_start_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_one_byte_integer packet_data property_start_index =
  push_frame ();
  let one_byte_integer: U8.t = packet_data.(U32.add property_start_index 1ul) in
  pop_frame ();
  let one_byte_integer_struct: struct_one_byte_integer = {
    one_byte_integer_value = one_byte_integer;
  } in
  let b: struct_property_type = property_struct_type_base in
  let property_struct_type_base: struct_property_type = {
    one_byte_integer_struct = one_byte_integer_struct;
    two_byte_integer_struct = {
      two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
    };
    four_byte_integer_struct = {
      four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
    };
    utf8_encoded_string_struct = {
      utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
      utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
      utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
    };
    variable_byte_integer_struct = {
      variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
    };
    binary_data_struct = {
      binary_length = b.binary_data_struct.binary_length;
      binary_value = b.binary_data_struct.binary_value;
    };
    utf8_string_pair_struct = {
      utf8_string_pair_key = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
      };
      utf8_string_pair_value = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
      };
    };
    property_type_error_code = 0uy;
  } in property_struct_type_base

val parse_property_variable_byte_integer: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> property_start_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_variable_byte_integer packet_data packet_size property_start_index =
  let variable_length: struct_variable_length = 
    get_variable_byte packet_data packet_size (U32.add property_start_index 1ul) in
  let property_variable_value: type_remaining_length = variable_length.variable_length_value in
  let variable_value_struct: struct_variable_byte_integer = {
    variable_byte_integer_value = property_variable_value;
  } in
  let next_start_index: U32.t = variable_length.next_start_index in
  let is_error: bool = (variable_length.have_error || next_start_index = 0ul) in
  let b: struct_property_type = property_struct_type_base in
  let property_struct_type_base: struct_property_type = {
    one_byte_integer_struct = {
      one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
    };
    two_byte_integer_struct = {
      two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
    };
    four_byte_integer_struct = {
      four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
    };
    utf8_encoded_string_struct = {
      utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
      utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
      utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
    };
    variable_byte_integer_struct = variable_value_struct;
    binary_data_struct = {
      binary_length = b.binary_data_struct.binary_length;
      binary_value = b.binary_data_struct.binary_value;
    };
    utf8_string_pair_struct = {
      utf8_string_pair_key = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
      };
      utf8_string_pair_value = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
      };
    };
    property_type_error_code = 
      (
        if (is_error) then 1uy
        else 0uy
      );
  } in property_struct_type_base

val parse_property_binary: packet_data: (B.buffer U8.t) 
  -> property_length: U32.t
  -> property_start_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_binary packet_data property_length property_start_index =
  push_frame ();
  // TODO: エラーチェック
  let binary_length_msb_u8: U8.t = packet_data.(U32.add property_start_index 1ul) in
  let binary_length_lsb_u8: U8.t = packet_data.(U32.add property_start_index 2ul) in
  let binary_length: U32.t = get_two_byte_integer_u8_to_u32 binary_length_msb_u8 binary_length_lsb_u8 in
  let payload_start_index: U32.t = U32.add property_start_index 3ul in
  let payload_end_index: U32.t = U32.add payload_start_index (U32.sub binary_length 1ul) in
  pop_frame ();
  let payload_struct: struct_payload = 
    get_payload packet_data payload_start_index payload_end_index in
  print_buffer_u8 payload_struct.payload payload_struct.
  payload_length;
  let binary_data_struct: struct_binary_data = {
    binary_length = uint32_to_uint16 payload_struct.payload_length;
    binary_value = payload_struct.payload;
  } in
  let b: struct_property_type = property_struct_type_base in
  let property_struct_type_base: struct_property_type = {
    one_byte_integer_struct = {
      one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
    };
    two_byte_integer_struct = {
      two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
    };
    four_byte_integer_struct = {
      four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
    };
    utf8_encoded_string_struct = {
      utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
      utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
      utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
    };
    variable_byte_integer_struct = {
      variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
    };
    binary_data_struct = binary_data_struct;
    utf8_string_pair_struct = {
      utf8_string_pair_key = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
      };
      utf8_string_pair_value = {
        utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
        utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
        utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
      };
    };
    property_type_error_code = 0uy;
  } in property_struct_type_base

val u8_array_to_u16_array: u8_array: (B.buffer U8.t)
  -> u8_array_length: U32.t
  -> u8_array_start_index: U32.t
  -> Stack (u16_array: struct_array_u16)
    (requires fun h0 -> B.live h0 u8_array)
    (ensures fun h0 r h1 -> true)
let u8_array_to_u16_array u8_array u8_array_length u8_array_start_index =
  push_frame ();
  let array_length_u16: U32.t  = 
    (
      if U32.eq (U32.rem u8_array_length 2ul) 0ul then
        (
          U32.div u8_array_length 2ul
        )
      else
        (
          U32.div (U32.add u8_array_length 1ul) 2ul
        )
    ) in 
  let u16_array: B.buffer U16.t = B.alloca 0us array_length_u16 in
  let ptr_counter: B.buffer U32.t = B.alloca 0ul 1ul in
  let inv h (i: nat) = B.live h u8_array /\
  B.live h ptr_counter in
  let body (i): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
    (
      let counter: U32.t = ptr_counter.(0ul) in
      if U32.eq (U32.rem (U32.sub i u8_array_start_index) 2ul) 1ul then
        (
          let two_byte_integer: U16.t = 
            get_two_byte_integer_u8_to_u16 u8_array.(U32.sub i 1ul) u8_array.(i) in
          u16_array.(counter) <- two_byte_integer;

          ptr_counter.(0ul) <- U32.add counter 1ul
        )
      else
        (
          if U32.eq i (U32.sub u8_array_length 1ul) then
            (
              let u8_integer: U8.t = u8_array.(i) in
              let u16_integer: U16.t = uint8_to_uint16 u8_integer in

              u16_array.(counter) <- u16_integer
            )
        )
    )
    in
    C.Loops.for u8_array_start_index (U32.add u8_array_start_index u8_array_length) inv body;
  pop_frame();
  {
   array_u16 = u16_array;
   array_length_u16 = array_length_u16;
  }

val is_valid_utf8_encoded_string: packet_data: (B.buffer U8.t) 
  -> utf8_encoded_string_start_index: U32.t
  -> utf8_encoded_string_end_index: U32.t
  -> Stack (utf8_encoded_string_struct: struct_utf8_string)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let is_valid_utf8_encoded_string packet_data utf8_encoded_string_start_index utf8_encoded_string_end_index =
  push_frame ();
  let utf8_encoded_string_entity_start_index: U32.t = 
    U32.add utf8_encoded_string_start_index 2ul in

  let utf8_entity_length_u32: U32.t = 
    U32.(utf8_encoded_string_end_index -^ utf8_encoded_string_entity_start_index +^ 1ul) in

  let is_malformed_utf8: B.buffer bool = B.alloca false 1ul in
  let codelen: B.buffer U8.t = B.alloca 0uy 1ul in
  let codepoint: B.buffer U16.t = B.alloca 0us 1ul in
  let i: B.buffer U32.t = B.alloca utf8_encoded_string_entity_start_index 1ul in

  // if(len < 0 || len > 65536) return MOSQ_ERR_INVAL;

  let inv h (counter: nat) = B.live h packet_data in
  let body (counter): Stack unit
    (requires (fun h -> inv h (U32.v counter)))
    (ensures (fun _ _ _ -> true)) =
    if (U32.gte i.(0ul) (U32.add utf8_encoded_string_end_index 1ul) || is_malformed_utf8.(0ul)) then
      ()
    else
      (
        let one_byte: U8.t = packet_data.(i.(0ul)) in

        if (U8.eq one_byte 0uy) then
          (
            print_string "a\n";
            is_malformed_utf8.(0ul) <- true
          )
        else if (U8.lte one_byte 0x7fuy) then
          (
            codelen.(0ul) <- 1uy;
            codepoint.(0ul) <- uint8_to_uint16 one_byte
          )
        else if(U8.eq (U8.logand one_byte 0xE0uy) 0xC0uy) then
          (
            // 110xxxxx - 2 byte sequence */
            if (U8.eq one_byte 0xC0uy || U8.eq one_byte 0xC1uy) then
              (
                // Invalid bytes */
                print_string "b\n";
                is_malformed_utf8.(0ul) <- true
              )
            else
              (
                codelen.(0ul) <- 2uy;
                codepoint.(0ul) <- uint8_to_uint16 (U8.logand one_byte 0x1Fuy)
              )
          )
        else if(U8.eq (U8.logand one_byte 0xF0uy) 0xE0uy) then
          (
            // 1110xxxx - 3 byte sequence */
            codelen.(0ul) <- 3uy;
            codepoint.(0ul) <- uint8_to_uint16 (U8.logand one_byte 0x0Fuy)
          )
        else if(U8.eq (U8.logand one_byte 0xF8uy) 0xF0uy) then
          (
            // 11110xxx - 4 byte sequence */
            if(U8.gt one_byte 0xF4uy) then
              (
                // Invalid, this would produce values > 0x10FFFF. */
                print_string "c\n";
                is_malformed_utf8.(0ul) <- true
              )
            else
              (
                codelen.(0ul) <- 4uy;
                codepoint.(0ul) <- uint8_to_uint16 (U8.logand one_byte 0x07uy)
              )
          )
        else
          (
            // Unexpected continuation byte. */
            print_string "d\n";
            is_malformed_utf8.(0ul) <- true
          );

        // Reconstruct full code point */
        let codelen_u8: U8.t = codelen.(0ul) in
        let codelen_u32: U32.t = uint8_to_uint32 codelen_u8 in

        if (U32.eq i.(0ul) U32.((U32.add utf8_encoded_string_end_index 1ul) -^ codelen_u32 +^ 1ul)) then
          (
            // Not enough data */
            print_string "e\n";
            is_malformed_utf8.(0ul) <- true
          )
        else
          (
            let inv2 h (j: nat) = B.live h packet_data in
            let body2 (j): Stack unit
              (requires (fun h -> inv2 h (U32.v j)))
              (ensures (fun _ _ _ -> true)) =
                (
                  // i+= 1
                  i.(0ul) <- U32.add i.(0ul) 1ul;

                  let next_one_byte: U8.t = packet_data.(i.(0ul)) in
                  // print_bool next_one_byte;
                  // print_hex_u16 (U16.logand next_one_byte 0xC0us);
                  if (not (U8.eq (U8.logand next_one_byte 0xC0uy) 0x80uy)) then
                    (
                      // Not a continuation byte */
                      print_string "f\n";
                      is_malformed_utf8.(0ul) <- true
                    )
                  else
                    (
                      let next_one_byte_u16: U16.t = uint8_to_uint16 next_one_byte in
                      codepoint.(0ul) 
                        <- U16.logor (U16.shift_left codepoint.(0ul) 6ul) (U16.logand next_one_byte_u16 0x3Fus)
                    )
                ) in
            let last_u8: U8.t = (U8.sub codelen.(0ul) 1uy) in

            let last_u32: U32.t = uint8_to_uint32 last_u8 in
            C.Loops.for 0ul last_u32 inv2 body2;

            
            // Check for UTF-16 high/low surrogates */
            if (U16.gte codepoint.(0ul) 0xD800us && U16.lte codepoint.(0ul) 0xDFFFus) then
              (
                print_string "g\n";
                is_malformed_utf8.(0ul) <- true
              );

            // Check for overlong or out of range encodings */
            // Checking codelen == 2 isn't necessary here, because it is already
            //  * covered above in the C0 and C1 checks.
            //  * if(codelen == 2 && codepoint.(0ul) < 0x0080){
            //  *	 return MOSQ_ERR_MALFORMED_UTF8;
            //  * }else
            // */
            let codepoint_u16: U16.t = codepoint.(0ul) in
            let codepoint_u32: U32.t = uint16_to_uint32 codepoint_u16 in
            if (U8.eq codelen.(0ul) 3uy && U16.lt codepoint.(0ul) 0x0800us) then
              (
                print_string "h\n";
                is_malformed_utf8.(0ul) <- true
              )
            else if(U8.eq codelen.(0ul) 4uy && ( U32.lt codepoint_u32 0x10000ul || U32.gt codepoint_u32 0x10FFFFul)) then
              (
                print_string "i\n";
                is_malformed_utf8.(0ul) <- true
              );
            // Check for non-characters */
            if (U16.gte codepoint.(0ul) 0xFDD0us && U16.lte codepoint.(0ul) 0xFDEFus) then
              (
                print_string "j\n";
                is_malformed_utf8.(0ul) <- true
              );
            if(U16.eq (U16.logand codepoint.(0ul) 0xFFFFus) 0xFFFEus || U16.eq (U16.logand codepoint.(0ul) 0xFFFFus) 0xFFFFus) then
              (
                print_string "k\n";
                is_malformed_utf8.(0ul) <- true
              );
            // Check for control characters */
            if (U16.lte codepoint.(0ul) 0x001Fus || (U16.gte codepoint.(0ul) 0x007Fus && U16.lte codepoint.(0ul) 0x009Fus)) then
              (
                print_string "l\n";
                is_malformed_utf8.(0ul) <- true
              )
          );
          i.(0ul) <- U32.add i.(0ul) 1ul
          // is_malformed_utf8.(0ul) <- true
      )
  in
  C.Loops.for utf8_encoded_string_entity_start_index (U32.add utf8_encoded_string_end_index 1ul) inv body;
  let utf8_value: B.buffer U8.t = B.offset packet_data utf8_encoded_string_entity_start_index in
  let utf8_encoded_string_struct: struct_utf8_string = {
    utf8_string_length = uint32_to_uint16 utf8_entity_length_u32;
    utf8_string_value = utf8_value;
    utf8_string_status_code =
      if (is_malformed_utf8.(0ul)) then
        1uy
      else
        0uy
  } in 
  pop_frame ();
  utf8_encoded_string_struct

val parse_property_utf8_encoded_string: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size  
  -> property_start_index: U32.t
  -> property_end_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_utf8_encoded_string packet_data packet_size property_start_index property_end_index =
  push_frame ();
  let utf8_encoded_string_start_index: U32.t = U32.add property_start_index 1ul in
  let utf8_encoded_string_end_index: U32.t = property_end_index in
  let msb_u8: U8.t = packet_data.(utf8_encoded_string_start_index) in
  let lsb_u8: U8.t = packet_data.(U32.add utf8_encoded_string_start_index 1ul) in
  pop_frame ();
  let two_byte_integer: U32.t = get_two_byte_integer_u8_to_u32 msb_u8 lsb_u8 in
  let b: struct_property_type = property_struct_type_base in
  ( 
    if (U32.eq two_byte_integer U32.(utf8_encoded_string_end_index -^ utf8_encoded_string_start_index -^ 1ul)) then
      (
        let utf8_encoded_string_struct: struct_utf8_string = is_valid_utf8_encoded_string packet_data 
          utf8_encoded_string_start_index utf8_encoded_string_end_index in
        let property_struct_type_base: struct_property_type = {
          one_byte_integer_struct = {
            one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
          };
          two_byte_integer_struct = {
            two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
          };
          four_byte_integer_struct = {
            four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
          };
          utf8_encoded_string_struct = utf8_encoded_string_struct;
          variable_byte_integer_struct = {
            variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
          };
          binary_data_struct = {
            binary_length = b.binary_data_struct.binary_length;
            binary_value = b.binary_data_struct.binary_value;
          };
          utf8_string_pair_struct = {
            utf8_string_pair_key = {
              utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length;
              utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value;
              utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code;
            };
            utf8_string_pair_value = {
              utf8_string_length = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length;
              utf8_string_value = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value;
              utf8_string_status_code = b.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code;
            };
          };
          property_type_error_code = utf8_encoded_string_struct.utf8_string_status_code;
        } in property_struct_type_base
      )
    else
      (
        b
      )
  )

val parse_property_utf8_encoded_string_pair: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size  
  -> property_start_index: U32.t
  -> property_end_index: U32.t
  -> Stack (property_struct_type_base: struct_property_type)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property_utf8_encoded_string_pair packet_data packet_size property_start_index property_end_index =
  push_frame ();
  let utf8_encoded_string_pair_start_index: U32.t = U32.add property_start_index 1ul in
  let utf8_encoded_string_pair_end_index: U32.t = property_end_index in


  let fisrt_msb_u8: U8.t = packet_data.(utf8_encoded_string_pair_start_index) in
  let first_lsb_u8: U8.t = packet_data.(U32.add utf8_encoded_string_pair_start_index 1ul) in
  let fist_byte_integer: U32.t = get_two_byte_integer_u8_to_u32 fisrt_msb_u8 first_lsb_u8 in

  let second_msb_u8: U8.t = packet_data.( U32.(utf8_encoded_string_pair_start_index +^ fist_byte_integer +^ 2ul )) in
  let second_lsb_u8: U8.t = packet_data.( U32.(utf8_encoded_string_pair_start_index +^ fist_byte_integer +^ 3ul )) in
  let second_byte_integer: U32.t = get_two_byte_integer_u8_to_u32 second_msb_u8 second_lsb_u8 in
  let b: struct_property_type = property_struct_type_base in
  if (U32.eq U32.(fist_byte_integer +^ second_byte_integer +^ 4ul) (U32.sub property_end_index property_start_index)) then
    (
      let utf8_string_pair_key: struct_utf8_string = 
        is_valid_utf8_encoded_string packet_data 
          utf8_encoded_string_pair_start_index U32.(utf8_encoded_string_pair_start_index +^ fist_byte_integer +^ 1ul) in
      let utf8_string_pair_value: struct_utf8_string =
        is_valid_utf8_encoded_string packet_data 
          U32.(utf8_encoded_string_pair_start_index +^ fist_byte_integer +^ 2ul) utf8_encoded_string_pair_end_index in
      let utf8_string_pair: struct_utf8_string_pair = {
        utf8_string_pair_key = utf8_string_pair_key;
        utf8_string_pair_value = utf8_string_pair_value;
      } in
      let property_struct_type_base: struct_property_type = {
        one_byte_integer_struct = {
          one_byte_integer_value = b.one_byte_integer_struct.one_byte_integer_value;
        };
        two_byte_integer_struct = {
          two_byte_integer_value = b.two_byte_integer_struct.two_byte_integer_value;
        };
        four_byte_integer_struct = {
          four_byte_integer_value = b.four_byte_integer_struct.four_byte_integer_value;
        };
        utf8_encoded_string_struct = {
          utf8_string_length = b.utf8_encoded_string_struct.utf8_string_length;
          utf8_string_value = b.utf8_encoded_string_struct.utf8_string_value;
          utf8_string_status_code = b.utf8_encoded_string_struct.utf8_string_status_code;
        };
        variable_byte_integer_struct = {
          variable_byte_integer_value = b.variable_byte_integer_struct.variable_byte_integer_value;
        };
        binary_data_struct = {
          binary_length = b.binary_data_struct.binary_length;
          binary_value = b.binary_data_struct.binary_value;
        };
        utf8_string_pair_struct = utf8_string_pair;
        property_type_error_code = 
          (
            if (utf8_string_pair_key.utf8_string_status_code = 1uy||
             utf8_string_pair_value.utf8_string_status_code = 1uy) then
              1uy
            else
              0uy
          );
      } in property_struct_type_base
    )
  else
    (
      b
    )

val parse_property: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> property_length: U32.t
  -> property_start_index: U32.t
  -> Stack (property: struct_property)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let parse_property packet_data packet_size property_length property_start_index =
  push_frame ();
  let last: U32.t = U32.add property_length property_start_index in
  let property_id: U8.t = packet_data.(property_start_index) in
  let property_type_id: U8.t = get_property_type_id property_id in
  let property_end_index: U32.t = U32.(property_start_index +^ property_length -^ 1ul) in
  let property_type_struct: struct_property_type = (
    if property_type_id = 1uy then // One Byte Integer
      (
        parse_property_one_byte_integer packet_data property_start_index
      )
    else if property_type_id = 2uy then // Two Byte Integer
      (
        parse_property_two_byte_integer packet_data property_start_index
      )
    else if property_type_id = 3uy then // Four Byte Integer
      (
        parse_property_four_byte_integer packet_data property_start_index
      )
    else if property_type_id = 4uy then // UTF-8 Encoded String
      (
        parse_property_utf8_encoded_string
          packet_data packet_size property_start_index property_end_index
      )
    else if property_type_id = 5uy then // Variable Byte Integer
      (
        parse_property_variable_byte_integer packet_data packet_size property_start_index
      )
    else if property_type_id = 6uy then // Binary Data
      (
        parse_property_binary packet_data property_length property_start_index
      )
    else if property_type_id = 7uy then // UTF-8 String Pair
      (
        parse_property_utf8_encoded_string_pair
          packet_data packet_size property_start_index property_end_index
      )
    else 
      (
        property_struct_type_base
      )
  ) in
  pop_frame ();
  let property: struct_property = {
    property_id = property_id;
    property_type_id = property_type_id;
    property_type_struct = property_type_struct;
    payload_start_index = last;
  } in property
