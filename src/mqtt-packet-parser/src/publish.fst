module Publish

module U8 = FStar.UInt8

open C.String

open Const
open Common

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
