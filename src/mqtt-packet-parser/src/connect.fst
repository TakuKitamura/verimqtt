module Connect

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer

open C.String
open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.Int.Cast

open Const
open Common


val assemble_connect_struct: s: struct_connect_parts
  -> Pure struct_fixed_header
    (requires true)
    (ensures (fun r -> true))
let assemble_connect_struct s =
  let connect_constant: struct_fixed_header_constant = s.connect_connect_constant in
  let connect_flag: U8.t = s.connect_connect_flag in
  let user_name_flag: U8.t = slice_byte connect_flag 0uy 1uy in
  let password_flag: U8.t = slice_byte connect_flag 1uy 2uy in
  let will_retain_flag: U8.t = slice_byte connect_flag 2uy 3uy in
  let will_qos_flag: U8.t = slice_byte connect_flag 3uy 5uy in
  let will_flag: U8.t = slice_byte connect_flag 5uy 6uy in
  let clean_start_flag: U8.t = slice_byte connect_flag 6uy 7uy in
  let resreved_flag: U8.t = slice_byte connect_flag 7uy 8uy in
  let connect_property_id: U8.t = s.connect_connect_property_id in
  {
    message_type = connect_constant.message_type_constant;
    message_name = connect_constant.message_name_constant;
    flags = {
      flag = connect_constant.flags_constant.flag;
      dup_flag = connect_constant.flags_constant.dup_flag;
      qos_flag = connect_constant.flags_constant.qos_flag;
      retain_flag = connect_constant.flags_constant.retain_flag;
    };
    remaining_length = s.connect_remaining_length;
    connect = 
        {
          protocol_name = !$"MQTT";
          protocol_version = 5uy;
          flags = {
            connect_flag = connect_flag;
            user_name = user_name_flag;
            password = password_flag;
            will_retain = will_retain_flag;
            will_qos = will_qos_flag;
            will_flag = will_flag;
            clean_start = clean_start_flag;
          };
          keep_alive = s.connect_keep_alive;
          connect_topic_length = s.connect_connect_topic_length;
          connect_property =
          if (U8.eq connect_property_id define_connect_property_session_expiry_interval_id) then 
            define_struct_connect_property_session_expiry_interval
          else if (U8.eq connect_property_id define_connect_property_receive_maximum_id) then 
            define_struct_connect_property_receive_maximum
          else if (U8.eq connect_property_id define_connect_property_maximum_packet_size_id) then 
            define_struct_connect_property_maximum_packet_size
          else if (U8.eq connect_property_id define_connect_property_topic_alias_maximum_id) then 
            define_struct_connect_property_topic_alias_maximum
          else if (U8.eq connect_property_id define_connect_property_request_response_information_id) then 
            define_struct_connect_property_request_response_information
          else if (U8.eq connect_property_id define_connect_property_request_problem_information_id) then 
            define_struct_connect_property_request_problem_information    
          else if (U8.eq connect_property_id define_connect_property_user_property_id) then 
            define_struct_connect_property_user_property
          else if (U8.eq connect_property_id define_connect_property_authentication_method_id) then 
            define_struct_connect_property_authentication_method
          else
            define_struct_connect_property_authentication_data
        };
    publish = {
      topic_length = 0ul;
      topic_name = !$"";
      property_length = 0ul;
      payload = !$"";
      payload_length = 0ul;
      property_id = max_u8;
    };
    disconnect = define_struct_disconnect_error;
    error = {
      code = define_no_error_code;
      message = define_no_error;
    };
  }

val connect_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index:U32.t
  -> Stack (connect_packet_seed: struct_connect_packet_seed)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let connect_packet_parser packet_data packet_size next_start_index =
  push_frame ();
  let ptr_is_break: B.buffer bool = B.alloca false 1ul in
  let ptr_protocol_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_protocol_version_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_connect_flag: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_keep_alive: B.buffer U8.t = B.alloca 0uy 2ul in
  let ptr_connect_topic_length: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_connect_property_id: B.buffer U8.t = B.alloca 0uy 1ul in
  let inv h (i: nat) =
    B.live h packet_data /\
    B.live h ptr_is_break /\
    B.live h ptr_protocol_name_error_status /\
    B.live h ptr_protocol_version_error_status /\
    B.live h ptr_connect_flag /\
    B.live h ptr_keep_alive /\
    B.live h ptr_connect_topic_length /\
    B.live h ptr_connect_property_id
    in
  let body (i: U32.t{ 2 <= U32.v i && U32.v i < U32.v packet_size  }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let one_byte : U8.t = packet_data.(i) in
    let is_break: bool = ptr_is_break.(0ul) in
    if (is_break) then
      ()
    else
      (
        let variable_header_index = U32.sub i next_start_index in
        if (U32.lte variable_header_index 5ul) then
          (
            if (
              (U32.eq variable_header_index 0ul && not (U8.eq one_byte 0x00uy)) ||
              (U32.eq variable_header_index 1ul && not (U8.eq one_byte 0x04uy)) ||
              (U32.eq variable_header_index 2ul && not (U8.eq one_byte 0x4Duy)) ||
              (U32.eq variable_header_index 3ul && not (U8.eq one_byte 0x51uy)) ||
              (U32.eq variable_header_index 4ul && not (U8.eq one_byte 0x54uy)) ||
              (U32.eq variable_header_index 5ul && not (U8.eq one_byte 0x54uy))
              ) then
              (
                ptr_protocol_name_error_status.(0ul) <- 1uy;
                ptr_is_break.(0ul) <- true
              )
          )
          else if (U32.eq variable_header_index 6ul && not (U8.eq one_byte 0x05uy)) then
            (
              ptr_protocol_version_error_status.(0ul) <- 1uy;
              ptr_is_break.(0ul) <- true
            )
          else if (U32.eq variable_header_index 7ul) then
            (
              ptr_connect_flag.(0ul) <- one_byte
            )
          else if (U32.eq variable_header_index 8ul) then
            (
              ptr_keep_alive.(0ul) <- one_byte
            )
          else if (U32.eq variable_header_index 9ul) then
            (
              if (U8.lte one_byte 0x7Fuy) then
                (
                  ptr_keep_alive.(1ul) <- one_byte
                )
              // else 
              //   (
              //     // TODO: keep aliveが127以上の場合は未実装.
              //   )
            )
          else if (U32.eq variable_header_index 10ul) then
            (
              // TODO: topic length が一桁かつ, keep aliveが127以下の場合
              let variable_length: struct_variable_length = 
                        get_variable_byte packet_data packet_size i in
              ptr_connect_topic_length.(0ul) <- uint8_to_uint32 one_byte
            )
          else if (U32.eq variable_header_index 11ul) then
            (
              // TODO: topic length が一桁かつ, keep aliveが127以下の場合
              ptr_connect_property_id.(0ul) <- one_byte
            )
          // else
          //   (
          //     print_string "x: ";
          //     print_u8 one_byte;
          //     print_string ", index: ";
          //     print_u32 variable_header_index;
          //     print_string "\n"
          //   )
      )
  in
  C.Loops.for next_start_index packet_size inv body;

  let protocol_name_error_status: U8.t = ptr_protocol_name_error_status.(0ul) in
  let protocol_version_error_status: U8.t = ptr_protocol_version_error_status.(0ul) in
  let connect_flag: U8.t = ptr_connect_flag.(0ul) in
  let keep_alive_msb_u8: U8.t = ptr_keep_alive.(0ul) in
  let keep_alive_lsb_u8: U8.t = ptr_keep_alive.(1ul) in
  let connect_topic_length: U32.t = ptr_connect_topic_length.(0ul) in
  let connect_property_id: U8.t = ptr_connect_property_id.(0ul) in
  pop_frame ();

  let connect_packet_seed: struct_connect_packet_seed = {
    connect_seed_protocol_name_error_status = protocol_name_error_status;
    connect_seed_protocol_version_error_status = protocol_version_error_status;
    connect_seed_connect_flag = connect_flag;
    connect_seed_keep_alive_msb_u8 = keep_alive_msb_u8;
    connect_seed_keep_alive_lsb_u8 = keep_alive_lsb_u8;
    connect_seed_connect_topic_length = connect_topic_length;
    connect_seed_connect_property_id = connect_property_id;
  } in connect_packet_seed

val connect_packet_parse_result: (share_common_data: struct_share_common_data)
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> B.live h0 share_common_data.common_packet_data)
    (ensures fun h0 r h1 -> true)
let connect_packet_parse_result share_common_data =
  let connect_packet_seed: struct_connect_packet_seed = 
  connect_packet_parser share_common_data.common_packet_data share_common_data.common_packet_size  share_common_data.common_next_start_index in
  let connect_constant: struct_fixed_header_constant =
    get_struct_fixed_header_constant_except_publish share_common_data.common_message_type in
  let connect_flag: U8.t = connect_packet_seed.connect_seed_connect_flag in
  let user_name_flag: U8.t = slice_byte connect_flag 0uy 1uy in
  let password_flag: U8.t = slice_byte connect_flag 1uy 2uy in
  let will_retain_flag: U8.t = slice_byte connect_flag 2uy 3uy in
  let will_qos_flag: U8.t = slice_byte connect_flag 3uy 5uy in
  let will_flag: U8.t = slice_byte connect_flag 5uy 6uy in
  let clean_start_flag: U8.t = slice_byte connect_flag 6uy 7uy in
  let resreved_flag: U8.t = slice_byte connect_flag 7uy 8uy in
  let connect_property_id: U8.t = connect_packet_seed.connect_seed_connect_property_id in
  let keep_alive_msb_u32: U32.t = 
    uint8_to_uint32 connect_packet_seed.connect_seed_keep_alive_msb_u8  in
  let keep_alive_lsb_u32: U32.t = 
    uint8_to_uint32 connect_packet_seed.connect_seed_keep_alive_lsb_u8 in 
  let keep_alive: U32.t = 
    U32.logor (U32.shift_left keep_alive_msb_u32 8ul)keep_alive_lsb_u32 in

  let have_error: bool =
    (connect_packet_seed.connect_seed_protocol_name_error_status = 1uy) ||
    (connect_packet_seed.connect_seed_protocol_version_error_status = 1uy) ||
    (not (U8.eq resreved_flag 0uy) ) in
  if (have_error) then
    (
      let error_struct: struct_error_struct =
        (
          if (connect_packet_seed.connect_seed_protocol_name_error_status = 1uy) then
            {
              code = define_error_protocol_name_invalid_code;
              message = define_error_protocol_name_invalid;
            }
          else if (connect_packet_seed.connect_seed_protocol_version_error_status = 1uy) then
            {
              code = define_error_protocol_version_invalid_code;
              message = define_error_protocol_version_invalid;
            }
          else // if (not (U8.eq resreved_flag 0uy) ) then
            {
              code = define_error_connect_flag_invalid_code;
              message = define_error_connect_flag_invalid;
            }
        ) in error_struct_fixed_header error_struct
    )
  else
    (
      let ed_fixed_header_parts:
        struct_connect_parts = {
          connect_remaining_length = share_common_data.common_remaining_length;
          connect_connect_constant = connect_constant;
          connect_connect_flag = connect_flag;
          connect_keep_alive = keep_alive;
          connect_connect_topic_length = connect_packet_seed.connect_seed_connect_topic_length;
          connect_connect_property_id = connect_packet_seed.connect_seed_connect_property_id;
      } in
      assemble_connect_struct ed_fixed_header_parts            
    )