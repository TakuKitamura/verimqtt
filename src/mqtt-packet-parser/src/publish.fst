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
open Debug_FFI

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

val get_topic_name: packet_data: (B.buffer U8.t) 
  -> topic_name_start_index: U32.t
  -> topic_length: U32.t
  -> Stack (topic_name: struct_topic_name)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let get_topic_name packet_data topic_name_start_index topic_length =
  push_frame ();
  let ptr_counter: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_topic_name_u8: B.buffer U8.t = B.alloca 0uy 65536ul in
  let ptr_topic_name: B.buffer type_topic_name_restrict = B.alloca !$"" 1ul in
  let ptr_topic_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let inv h (i: nat) = B.live h packet_data /\
  B.live h ptr_counter /\
  B.live h ptr_topic_name_u8 /\
  B.live h ptr_topic_name /\
  B.live h ptr_topic_name_error_status in
  let body (i): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
    (
      let one_byte: U8.t = packet_data.(i) in 
      if (U8.eq one_byte 0x00uy || U8.eq one_byte 0x23uy || U8.eq one_byte 0x2buy) then
        (
          ptr_topic_name_error_status.(0ul) <- 2uy
        )
      else
        (
          // ptr_topic_name_u8.(U32.sub variable_header_index 2ul) <- one_byte;
          ptr_topic_name_u8.(ptr_counter.(0ul)) <- one_byte;
          // 0xEF 0xBB 0xBF は 0xFE 0xFF 置換
          if (ptr_counter.(0ul) = (U32.(topic_length -^ 1ul))) then
            (
              let topic_name: type_topic_name_restrict =
                (
                  if (ptr_topic_name_u8.(65535ul) = 0uy) then
                    let bom = replace_utf8_encoded ptr_topic_name_u8 65536ul in
                    // TODO: remaining length, ptr_topic_length も -1 対応させる?
                    // ptr_topic_length.(0ul) 
                    //   <- U32.sub ptr_topic_length.(0ul) bom.bom_count;
                    topic_name_uint8_to_c_string bom.replace_bom
                  else
                    (
                      ptr_topic_name_error_status.(0ul) <- 1uy;
                      !$""
                    )
                ) in ptr_topic_name.(0ul) <- topic_name
            )
          );
          ptr_counter.(0ul) <- U32.add ptr_counter.(0ul) 1ul
    )
  in
  let last: U32.t = U32.add topic_length topic_name_start_index in
  C.Loops.for topic_name_start_index last inv body;
  let topic_name: type_topic_name_restrict = ptr_topic_name.(0ul) in
  let topic_name_error_status: U8.t = ptr_topic_name_error_status.(0ul) in
  let topic_name: struct_topic_name = {
    topic_name_error_status = topic_name_error_status;
    topic_name = topic_name;
  } in topic_name

val publish_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index:U32.t
  -> Stack (publish_packet_seed: struct_publish_packet_seed)
    (requires fun h0 -> B.live h0 packet_data)
    (ensures fun h0 r h1 -> true)
let publish_packet_parser packet_data packet_size next_start_index =
  push_frame();

  let msb_u8: U8.t = packet_data.(next_start_index) in
  let lsb_u8: U8.t = packet_data.(U32.add next_start_index 1ul) in
  let msb_u32: U32.t = uint8_to_uint32 msb_u8  in
  let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
  let topic_length: U32.t =
    U32.logor (U32.shift_left msb_u32 8ul) lsb_u32 in
  
  let topic_name_struct: struct_topic_name = 
    get_topic_name packet_data (U32.add next_start_index 2ul) topic_length in
  let topic_name_error_status: U8.t = topic_name_struct.topic_name_error_status in

  let variable_length: struct_variable_length = 
    get_variable_byte 
      packet_data packet_size (U32.add (U32.add next_start_index 2ul) topic_length) in
  let property_length: type_remaining_length = 
    variable_length.variable_length_value in
  let property_start_index: U32.t = variable_length.next_start_index in
  let property_struct: struct_property = 
    parse_property packet_data property_length property_start_index in
  let property_id = property_struct.property_id in

  let payload_struct: struct_payload = 
    get_payload packet_data packet_size property_struct.payload_start_index in
    
  let payload_error_status = 
  if (payload_struct.is_valid_payload = false) then
    (
      1uy
    )
  else
    (
      0uy
    ) in
  pop_frame ();

  let publish_packet_seed: struct_publish_packet_seed = {
    publish_seed_topic_length = topic_length;
    publish_seed_topic_name = topic_name_struct.topic_name;
    publish_seed_topic_name_error_status = topic_name_error_status;
    publish_seed_is_searching_property_length = false;
    publish_seed_property_length = property_length;
    publish_seed_payload = 
      payload_uint8_to_c_string payload_struct.payload min_packet_size max_packet_size packet_size;
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
