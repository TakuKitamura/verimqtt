module Disconnect

open C.String

open Const
open Common
open FStar.HyperStack.ST
open LowStar.BufferOps

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer
#set-options "--z3rlimit 10000 --initial_fuel 10 --initial_ifuel 10"

val assemble_disconnect_struct: s: struct_disconnect_parts
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let assemble_disconnect_struct s =
  push_frame ();
  let disconnect_constant: struct_fixed_header_constant = s.disconnect_disconnect_constant in
  let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
  pop_frame ();
  {
    message_type = disconnect_constant.message_type_constant;
    message_name = disconnect_constant.message_name_constant;
    flags = {
      flag = disconnect_constant.flags_constant.flag;
      dup_flag = disconnect_constant.flags_constant.dup_flag;
      qos_flag = disconnect_constant.flags_constant.qos_flag;
      retain_flag = disconnect_constant.flags_constant.retain_flag;
    };
    remaining_length = s.disconnect_remaining_length;
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
      keep_alive = 0us;
      connect_id = 
        {
          utf8_string_length = 0us;
          utf8_string_value = empty_buffer;
          utf8_string_status_code = 1uy;
          utf8_next_start_index = 0ul;
        };
      will =
        {
          connect_will_property = property_struct_base;
          connect_will_topic_name = 
            {
              utf8_string_length = 0us;
              utf8_string_value = empty_buffer;
              utf8_string_status_code = 1uy;
              utf8_next_start_index = 0ul;
            };
          connect_will_payload = 
            {
              is_valid_binary_data = false;
              binary_length = 0us;
              binary_value = empty_buffer;
              binary_next_start_index = 0ul;
            };
          user_name_or_password_next_start_index = 0ul;
        };
        user_name =
          {
            utf8_string_length = 0us;
            utf8_string_value = empty_buffer;
            utf8_string_status_code = 1uy;
            utf8_next_start_index = 0ul;
          };
        password =
          {
            is_valid_binary_data = false;
            binary_length = 0us;
            binary_value = empty_buffer;
            binary_next_start_index = 0ul;
          };
    };
    publish = {
      topic_length = 0ul;
      topic_name = !$"";
      packet_identifier = max_u16;
      // property_length = 0ul;
      payload = {
        is_valid_payload = false;
        payload_value = empty_buffer;
        payload_length = 0ul;
      };
      // payload_length = 0ul;
      // property_id = max_u8;
    };
    disconnect = s.disconnect_struct;
    property = s.property;
    error = {
      code = define_no_error_code;
      message = define_no_error;
    };
  }

val get_disconnect_reason: reason_code: type_disconnect_reason_code 
  -> Stack (disconnect_reason_struct: struct_disconnect_reason)
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let get_disconnect_reason reason_code =
  let disconnect_reason_struct: struct_disconnect_reason =
    (
      if (U8.eq reason_code define_disconnect_reason_code_normal_disconnection) then
        define_struct_disconnect_normal_disconnection
      else if (U8.eq reason_code define_disconnect_reason_code_disconnect_with_will_message) then
        define_struct_disconnect_disconnect_with_will_message
      else if (U8.eq reason_code define_disconnect_reason_code_unspecified_error) then
        define_struct_disconnect_unspecified_error
      else if (U8.eq reason_code define_disconnect_reason_code_malformed_packet) then
        define_struct_disconnect_malformed_packet
      else if (U8.eq reason_code define_disconnect_reason_code_protocol_error) then
        define_struct_disconnect_protocol_error
      else if (U8.eq reason_code define_disconnect_reason_code_implementation_specific_error) then
        define_struct_disconnect_implementation_specific_error
      else if (U8.eq reason_code define_disconnect_reason_code_not_authorized) then
        define_struct_disconnect_not_authorized
      else if (U8.eq reason_code define_disconnect_reason_code_server_busy) then
        define_struct_disconnect_server_busy
      else if (U8.eq reason_code define_disconnect_reason_code_server_shutting_down) then
        define_struct_disconnect_server_shutting_down
      else if (U8.eq reason_code define_disconnect_reason_code_keep_alive_timeout) then
        define_struct_disconnect_keep_alive_timeout
      else if (U8.eq reason_code define_disconnect_reason_code_session_taken_over) then
        define_struct_disconnect_session_taken_over
      else if (U8.eq reason_code define_disconnect_reason_code_topic_filter_invalid) then
        define_struct_disconnect_topic_filter_invalid
      else if (U8.eq reason_code define_disconnect_reason_code_topic_name_invalid) then
        define_struct_disconnect_topic_name_invalid
      else if (U8.eq reason_code define_disconnect_reason_receive_maximum_exceeded) then
        define_struct_disconnect_receive_maximum_exceeded
      else if (U8.eq reason_code define_disconnect_reason_topic_alias_invalid) then
        define_struct_disconnect_topic_alias_invalid
      else if (U8.eq reason_code define_disconnect_reason_packet_too_large) then
        define_struct_disconnect_packet_too_large
      else if (U8.eq reason_code define_disconnect_reason_message_rate_too_high) then
        define_struct_disconnect_message_rate_too_high
      else if (U8.eq reason_code define_disconnect_reason_quota_exceeded) then
        define_struct_disconnect_quota_exceeded
      else if (U8.eq reason_code define_disconnect_reason_administrative_action) then
        define_struct_disconnect_administrative_action
      else if (U8.eq reason_code define_disconnect_reason_payload_format_invalid) then
        define_struct_disconnect_payload_format_invalid
      else if (U8.eq reason_code define_disconnect_reason_retain_not_supported) then
        define_struct_disconnect_retain_not_supported
      else if (U8.eq reason_code define_disconnect_reason_qos_not_supported) then
        define_struct_disconnect_qos_not_supported
      else if (U8.eq reason_code define_disconnect_reason_use_another_server) then
        define_struct_disconnect_use_another_server
      else if (U8.eq reason_code define_disconnect_reason_server_moved) then
        define_struct_disconnect_server_moved
      else if (U8.eq reason_code define_disconnect_reason_shared_subscriptions_not_supported) then
        define_struct_disconnect_shared_subscriptions_not_supported
      else if (U8.eq reason_code define_disconnect_reason_connection_rate_exceeded) then
        define_struct_disconnect_connection_rate_exceeded
      else if (U8.eq reason_code define_disconnect_reason_maximum_connect_time) then
        define_struct_disconnect_maximum_connect_time
      else if (U8.eq reason_code define_disconnect_reason_subscription_identifiers_not_supported) then
        define_struct_disconnect_subscription_identifiers_not_supported
      else if (U8.eq reason_code define_disconnect_reason_wildcard_subscriptions_not_supported) then
        define_struct_disconnect_wildcard_subscriptions_not_supported
      else
        define_struct_disconnect_error
    ) in disconnect_reason_struct

val disconnect_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index: type_packet_data_index
  -> Stack (disconnect_packet_seed: struct_disconnect_packet_seed)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 2))
    (ensures fun h0 r h1 -> true)
let disconnect_packet_parser packet_data packet_size next_start_index =
  push_frame ();
  let reason_code: type_disconnect_reason_code = packet_data.(next_start_index) in
  let disconnect_reason_struct: struct_disconnect_reason = get_disconnect_reason reason_code in
  let property_start_index: type_packet_data_index = U32.add next_start_index 1ul in
  let property_struct: struct_property = 
    parse_property packet_data packet_size property_start_index in
  pop_frame ();
  let disconnect_packet_seed_struct :struct_disconnect_packet_seed = 
    {
      disconnect_seed_reason = disconnect_reason_struct;
      disconnect_seed_property = property_struct;
    } in disconnect_packet_seed_struct

val disconnect_packet_parse_result: (share_common_data: struct_share_common_data)
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> 
    logic_packet_data h0 share_common_data.common_packet_data share_common_data.common_packet_size /\
    U32.v share_common_data.common_next_start_index < (B.length share_common_data.common_packet_data - 2))
    (ensures fun h0 r h1 -> true)
let disconnect_packet_parse_result share_common_data =
  // Reason Code, Property ともに省略
  let disconnect_constant: struct_fixed_header_constant =
    get_struct_fixed_header_constant_except_publish share_common_data.common_message_type in
  if (share_common_data.common_remaining_length = 0ul) then
    (
      let disconnect_struct: struct_disconnect = {
        disconnect_reason = define_struct_disconnect_normal_disconnection;
      } in
      let ed_fixed_header_parts: struct_disconnect_parts = {
        disconnect_disconnect_constant = disconnect_constant;
        disconnect_remaining_length = share_common_data.common_remaining_length;
        disconnect_struct = disconnect_struct;
        property = property_struct_base;
      } in
      assemble_disconnect_struct ed_fixed_header_parts
    )
  else 
    (
      let disconnect_packet_seed: struct_disconnect_packet_seed = 
        disconnect_packet_parser
          share_common_data.common_packet_data
          share_common_data.common_packet_size 
          share_common_data.common_next_start_index in
      let disconnect_reason: struct_disconnect_reason = disconnect_packet_seed.disconnect_seed_reason in
      let disconnect_property: struct_property = disconnect_packet_seed.disconnect_seed_property in
      let have_error: bool =
        (
          disconnect_reason.disconnect_reason_code = max_u8 ||
          U8.gt disconnect_property.property_type_struct.property_type_error.property_error_code 0uy
        ) in
        if (have_error) then
          (
            let error_struct: struct_error_struct =
              if (disconnect_reason.disconnect_reason_code = max_u8) then
                {
                    code = define_error_disconnect_reason_invalid_code;
                    message = define_error_disconnect_reason_invalid;
                }
              else // if (U8.gt disconnect_property.property_type_struct.property_type_error.property_error_code 0uy) then
                {
                  code = define_error_property_error_code;
                  message = disconnect_property.property_type_struct.property_type_error.property_error_code_name;
                }
            in error_struct_fixed_header error_struct
          )
        else
          (
            let disconnect_struct: struct_disconnect = {
              disconnect_reason = disconnect_reason;
            } in
            let ed_fixed_header_parts:
            struct_disconnect_parts = {
              disconnect_disconnect_constant = disconnect_constant;
              disconnect_remaining_length = share_common_data.common_remaining_length;
              disconnect_struct = disconnect_struct;
              property = disconnect_property;
            } in
            assemble_disconnect_struct ed_fixed_header_parts
          )
    )