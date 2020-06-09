module Disconnect

open C.String
open Const

module U8 = FStar.UInt8

val assemble_disconnect_struct: s: struct_disconnect_parts
  -> Pure struct_fixed_header
    (requires true)
    (ensures (fun r -> true))
let assemble_disconnect_struct s =
    let disconnect_constant: struct_fixed_header_constant = s.disconnect_disconnect_constant in
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
      disconnect = (
        if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_normal_disconnection) then
          define_struct_disconnect_normal_disconnection

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_disconnect_with_will_message) then
          define_struct_disconnect_disconnect_with_will_message

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_unspecified_error) then
          define_struct_disconnect_unspecified_error

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_malformed_packet) then
          define_struct_disconnect_malformed_packet

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_protocol_error) then
          define_struct_disconnect_protocol_error

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_implementation_specific_error) then
          define_struct_disconnect_implementation_specific_error

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_not_authorized) then
          define_struct_disconnect_not_authorized

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_server_busy) then
          define_struct_disconnect_server_busy

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_server_shutting_down) then
          define_struct_disconnect_server_shutting_down

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_keep_alive_timeout) then
            define_struct_disconnect_keep_alive_timeout

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_session_taken_over) then
            define_struct_disconnect_session_taken_over
            
        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_topic_filter_invalid) then
            define_struct_disconnect_topic_filter_invalid
        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_code_topic_name_invalid) then
            define_struct_disconnect_topic_name_invalid

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_receive_maximum_exceeded) then
            define_struct_disconnect_receive_maximum_exceeded

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_topic_alias_invalid) then
            define_struct_disconnect_topic_alias_invalid

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_packet_too_large) then
            define_struct_disconnect_packet_too_large

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_message_rate_too_high) then
            define_struct_disconnect_message_rate_too_high

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_quota_exceeded) then
            define_struct_disconnect_quota_exceeded

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_administrative_action) then
            define_struct_disconnect_administrative_action

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_payload_format_invalid) then
            define_struct_disconnect_payload_format_invalid

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_retain_not_supported) then
            define_struct_disconnect_retain_not_supported

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_qos_not_supported) then
            define_struct_disconnect_qos_not_supported

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_use_another_server) then
            define_struct_disconnect_use_another_server

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_server_moved) then
            define_struct_disconnect_server_moved

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_shared_subscriptions_not_supported) then
            define_struct_disconnect_shared_subscriptions_not_supported

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_connection_rate_exceeded) then
            define_struct_disconnect_connection_rate_exceeded

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_maximum_connect_time) then
            define_struct_disconnect_maximum_connect_time

        else if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_subscription_identifiers_not_supported) then
            define_struct_disconnect_subscription_identifiers_not_supported

        else // if (U8.eq disconnect_constant.flags_constant.flag define_disconnect_reason_wildcard_subscriptions_not_supported) then
            define_struct_disconnect_wildcard_subscriptions_not_supported
      );

      error = {
        code = define_no_error_code;
        message = define_no_error;
      };
    }
