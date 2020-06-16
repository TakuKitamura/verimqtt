module Publish

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer

open C.String
open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.Int.Cast
open LowStar.Printf

open Const
open Common
open FFI
open Debug

val get_dup_flag: fixed_header_first_one_byte: U8.t -> type_dup_flags_restrict
let get_dup_flag fixed_header_first_one_byte =
  let dup_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 4uy 5uy in
  if (U8.gt dup_flag_bits 1uy) then
    max_u8
  else
    dup_flag_bits

val get_qos_flag: fixed_header_first_one_byte: U8.t -> type_qos_flags_restrict
let get_qos_flag fixed_header_first_one_byte =
    let qos_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 5uy 7uy in
    if (U8.gt qos_flag_bits 2uy) then
      max_u8
    else
      qos_flag_bits

val get_retain_flag: fixed_header_first_one_byte: U8.t -> type_retain_flags_restrict
let get_retain_flag fixed_header_first_one_byte =
    let retain_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 7uy 8uy in
    if (U8.gt retain_flag_bits 1uy) then
      max_u8
    else
      retain_flag_bits

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

val assemble_publish_struct: s: struct_publish_parts
  -> Pure struct_fixed_header
    (requires true)
    (ensures (fun r -> true))
let assemble_publish_struct s =
      let dup_flag: type_dup_flags_restrict = get_dup_flag s.publish_fixed_header_first_one_byte in
      let qos_flag: type_qos_flags_restrict = get_qos_flag s.publish_fixed_header_first_one_byte in
      let retain_flag: type_retain_flags_restrict = get_retain_flag s.publish_fixed_header_first_one_byte in
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
          remaining_length = s.publish_remaining_length;
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
              connect_property_name = !$""
            }
          };
          publish = {
            topic_length = s.publish_topic_length;
            topic_name = s.publish_topic_name;
            property_length = s.publish_property_length;
            property_id = s.publish_property_id;
            payload = s.publish_payload;
          };
          disconnect = {
            disconnect_reason_code = max_u8;
            disconnect_reason_code_name = !$"";
          };
          error = {
            code = define_no_error_code;
            message = define_no_error;
          };
        }

val publish_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index:U32.t
  -> Stack (publish_packet_seed: struct_publish_packet_seed)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let publish_packet_parser packet_data packet_size next_start_index =
  push_frame();
  let ptr_is_break: B.buffer bool = B.alloca false 1ul in
  let ptr_for_topic_length: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_topic_length: B.buffer type_topic_length_restrict = B.alloca max_u32 1ul in
  let ptr_topic_name_u8: B.buffer U8.t = B.alloca 0uy 65536ul in
  let ptr_topic_name: B.buffer type_topic_name_restrict = B.alloca !$"" 1ul in
  let ptr_topic_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_property_length: B.buffer type_property_length = B.alloca 0ul 1ul in
  let ptr_is_searching_property_length: B.buffer bool = B.alloca true 1ul in
  let ptr_payload: B.buffer type_payload_restrict = B.alloca !$"" 1ul in
  let ptr_payload_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_next_start_index: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_property_id: B.buffer U8.t = B.alloca max_u8 1ul in

  let inv h (i: nat) =
    B.live h packet_data /\
    B.live h ptr_is_break /\
    B.live h ptr_for_topic_length /\
    B.live h ptr_topic_length /\
    B.live h ptr_topic_name_u8 /\
    B.live h ptr_topic_name /\
    B.live h ptr_topic_name_error_status /\
    B.live h ptr_property_length /\
    B.live h ptr_is_searching_property_length /\
    B.live h ptr_payload /\
    B.live h ptr_payload_error_status /\
    B.live h ptr_next_start_index /\
    B.live h ptr_property_id
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
        let topic_length: type_topic_length_restrict = ptr_topic_length.(0ul) in
        if (variable_header_index = 0ul) then
          ptr_for_topic_length.(0ul) <- one_byte
        else if (variable_header_index = 1ul) then
          (
            let msb_u8: U8.t = ptr_for_topic_length.(0ul) in
            let lsb_u8: U8.t = one_byte in
            let msb_u32: U32.t = uint8_to_uint32 msb_u8  in
            let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
            let _topic_length: U32.t =
              U32.logor (U32.shift_left msb_u32 8ul) lsb_u32 in
            if (U32.gt _topic_length 65535ul) then
              (
                ptr_topic_length.(0ul) <- max_u32;
                ptr_is_break.(0ul) <- true
              )
            else
              (
                ptr_topic_length.(0ul) <- _topic_length
              )
          )
        else if (U32.gte variable_header_index 2ul) then
          (
            let is_searching_property_length: bool =
              ptr_is_searching_property_length.(0ul) in
            if (topic_length = max_u32) then
              (
                ptr_topic_length.(0ul) <- max_u32;
                ptr_is_break.(0ul) <- true
              )
            else
              (
              if (U32.lte variable_header_index (U32.(topic_length +^ 1ul))) then
                (
                  if (U8.eq one_byte 0x00uy || U8.eq one_byte 0x23uy || U8.eq one_byte 0x2buy) then
                    (
                      ptr_topic_name_error_status.(0ul) <- 2uy;
                      ptr_is_break.(0ul) <- true
                    )
                  else
                    (
                      ptr_topic_name_u8.(U32.sub variable_header_index 2ul) <- one_byte;
                      // 0xEF 0xBB 0xBF は 0xFE 0xFF 置換
                      if (variable_header_index = (U32.(topic_length +^ 1ul))) then
                        (
                          let topic_name: type_topic_name_restrict =
                            (
                              if (ptr_topic_name_u8.(65535ul) = 0uy) then
                                let replace_bom = replace_utf8_encoded ptr_topic_name_u8 65536ul in
                                topic_name_uint8_to_c_string replace_bom
                              else
                                (
                                  ptr_topic_name_error_status.(0ul) <- 1uy;
                                  !$""
                                )
                            ) in ptr_topic_name.(0ul) <- topic_name
                        )
                      )
                )
              else if (U32.gt variable_header_index (U32.(topic_length +^ 1ul))
                && U32.lte variable_header_index (U32.(topic_length +^ 5ul))
                && is_searching_property_length
                ) then
                (
                  let variable_length: struct_variable_length = 
                    get_variable_byte packet_data packet_size i in
                  let property_length: type_remaining_length = 
                    variable_length.variable_length_value in
                  let next_start_index: U32.t = variable_length.next_start_index in
                  print_u32 property_length;
                  print_string "<- property_length\n";
                  print_u32 next_start_index;
                  print_string "<- next_start_index\n";

                  ptr_property_length.(0ul) <- uint8_to_uint32 one_byte;
                  ptr_next_start_index.(0ul) <- next_start_index;
                  ptr_is_searching_property_length.(0ul) <- false
                )
              else if (not is_searching_property_length) then
                (
                  print_u32 i;
                  print_string "<- i\n";
                  if (U32.lt i (U32.add ptr_next_start_index.(0ul) ptr_property_length.(0ul))) then
                    (
                      if (U32.eq i ptr_next_start_index.(0ul)) then
                        (
                          print_hex one_byte;
                          ptr_property_id.(0ul) <- one_byte;
                          print_string "<- id\n"
                        ) 
                      else
                        (
                          print_hex one_byte;
                          print_string "<- one_byte\n"           
                        )
                    )
                  else 
                    (
                      let payload_offset: type_payload_offset = i in
                      let ptr_payload_u8: B.buffer U8.t = B.offset packet_data payload_offset in
                      let payload: type_payload_restrict =
                        (
                          let last_payload_index: U32.t =
                            U32.(packet_size -^ payload_offset) in
                          let last_payload_element: U8.t = ptr_payload_u8.(last_payload_index) in
                            if (last_payload_element <> 0uy) then
                              (
                                ptr_payload_error_status.(0ul) <- 1uy;
                                !$""
                              )
                            else
                              payload_uint8_to_c_string ptr_payload_u8 min_packet_size max_packet_size packet_size
                        ) in
                      ptr_payload.(0ul) <- payload;
                      ptr_is_break.(0ul) <- true
                     )
                )
              else
                (
                  ()
                )
              )
          )
        else
          (
            ()
          )
      )
  in
  C.Loops.for next_start_index packet_size inv body;
  pop_frame ();

  let topic_length: type_topic_length_restrict = ptr_topic_length.(0ul) in
  let topic_name: type_topic_name_restrict = ptr_topic_name.(0ul) in
  let topic_name_error_status: U8.t = ptr_topic_name_error_status.(0ul) in
  let is_searching_property_length: bool = ptr_is_searching_property_length.(0ul) in
  let property_length: type_property_length = ptr_property_length.(0ul) in
  let payload: type_payload_restrict = ptr_payload.(0ul) in
  let payload_error_status: U8.t = ptr_payload_error_status.(0ul) in
  let property_id: U8.t = ptr_property_id.(0ul) in

  let publish_packet_seed: struct_publish_packet_seed = {
    publish_seed_topic_length = topic_length;
    publish_seed_topic_name = topic_name;
    publish_seed_topic_name_error_status = topic_name_error_status;
    publish_seed_is_searching_property_length = is_searching_property_length;
    publish_seed_property_length = property_length;
    publish_seed_payload = payload;
    publish_seed_payload_error_status = payload_error_status;
    publish_seed_property_id = property_id;
  } in publish_packet_seed

val publish_packet_parse_result: (share_common_data: struct_share_common_data)
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> B.live h0 share_common_data.common_packet_data)
    (ensures fun h0 r h1 -> true)
let publish_packet_parse_result share_common_data =
  let publish_packet_seed: struct_publish_packet_seed = 
    publish_packet_parser share_common_data.common_packet_data share_common_data.common_packet_size share_common_data.common_next_start_index in
  let first_one_byte: U8.t = share_common_data.common_first_one_byte in
  let dup_flag: type_dup_flags_restrict = get_dup_flag first_one_byte in
  let qos_flag: type_qos_flags_restrict = get_qos_flag first_one_byte in
  let retain_flag: type_retain_flags_restrict = get_retain_flag first_one_byte in
  let have_error: bool =
    (U8.eq dup_flag max_u8) ||
    (U8.eq qos_flag max_u8) ||
    (U8.eq retain_flag max_u8) ||
    (U32.eq publish_packet_seed.publish_seed_topic_length max_u32) ||
    (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 1uy) ||
    (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 2uy) ||
    (publish_packet_seed.publish_seed_is_searching_property_length) ||
    (U8.gt publish_packet_seed.publish_seed_payload_error_status 0uy) in
  if (have_error) then
    (
      let error_struct: struct_error_struct =
        (
          if (U8.eq dup_flag max_u8) then
            {
              code = define_error_dup_flag_invalid_code;
              message = define_error_dup_flag_invalid;
            }
          else if (U8.eq qos_flag max_u8) then
            {
              code = define_error_qos_flag_invalid_code;
              message = define_error_qos_flag_invalid;
            }
          else if (U8.eq retain_flag max_u8) then
            {
              code = define_error_retain_flag_invalid_code;
              message = define_error_retain_flag_invalid;
            }
          else if (U32.eq publish_packet_seed.publish_seed_topic_length max_u32) then
            {
              code = define_error_topic_length_invalid_code;
              message = define_error_topic_length_invalid;
            }
          else if (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 1uy) then
            {
              code = define_error_topic_name_dont_zero_terminated_code;
              message = define_error_topic_name_dont_zero_terminated;
            }
          else if (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 2uy) then
            {
              code = define_error_topic_name_have_inavlid_character_code;
              message = define_error_topic_name_have_inavlid_character;
            }
          else // if (is_searching_property_length) then
            {
              code = define_error_property_length_invalid_code;
              message = define_error_property_length_invalid;
            }
        ) in error_struct_fixed_header error_struct
    )
  else
    (
      let ed_fixed_header_parts:
        struct_publish_parts = {
          publish_fixed_header_first_one_byte = first_one_byte;
          publish_remaining_length = share_common_data.common_remaining_length;
          publish_topic_length = publish_packet_seed.publish_seed_topic_length;
          publish_topic_name = publish_packet_seed.publish_seed_topic_name;
          publish_property_length = publish_packet_seed.publish_seed_property_length;
          publish_payload = publish_packet_seed.publish_seed_payload;
          publish_property_id = publish_packet_seed.publish_seed_property_id;
      } in
      assemble_publish_struct ed_fixed_header_parts
    )
