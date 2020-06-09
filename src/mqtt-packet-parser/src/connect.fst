module Connect

open Const
open Common

open C.String

module U8 = FStar.UInt8

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
      topic_length = max_u32;
      topic_name = !$"";
      property_length = max_u32;
      payload = !$"";
    };
    disconnect = define_struct_disconnect_error;
    error = {
      code = define_no_error_code;
      message = define_no_error;
    };
  }